# Assembler Verification Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task.

**Goal:** Formally prove assembler correctness — 5 theorems, 0 sorry.

**Design doc:** `docs/plans/2026-02-24-assembler-verification-design.md`

**Project root:** `/Users/nick/dev/essential/lemma`
**Build command:** `~/.elan/bin/lake build`
**VCS:** jj (Jujutsu) — NOT git. Use `jj commit -m "msg"` to commit, `jj status` to check status.

---

## Task 1: Refactor Assembler to List UInt8

**Files:**
- Modify: `Lemma/EVM/Asm.lean`

**Step 1: Refactor `assemble` to return `Option (List UInt8)`**

Change the `emit` inner function from `ByteArray` accumulator to `List UInt8` accumulator. Change `acc.push` calls to `acc ++ [...]`. Return type becomes `Option (List UInt8)`.

Add `assembleBytes` wrapper:
```lean
def assembleBytes (items : List AsmItem) : Option ByteArray :=
  (assemble items).map fun bs => ⟨bs.toArray⟩
```

**Step 2: Verify it compiles**

Run: `~/.elan/bin/lake build Lemma.EVM.Asm`

**Step 3: Commit**

```bash
jj commit -m "refactor(evm): assembler returns List UInt8 for provability"
```

---

## Task 2: Update Consumers (Contract.lean, Hex.lean)

**Files:**
- Modify: `Lemma/EVM/Codegen/Contract.lean`
- Modify: `Lemma/EVM/Hex.lean`

**Step 1: Update Contract.lean**

`deployCode` calls `assemble runtimeCode` which now returns `Option (List UInt8)`.

Update:
- `runtimeBytes.size` → `runtimeBytes.length`
- `runtimeBytes.size.toUInt8` → `runtimeBytes.length.toUInt8`
- Final concatenation: `some ⟨(preamble ++ runtimeBytes).toArray⟩`

The function still returns `Option ByteArray` — the conversion happens at the boundary.

**Step 2: Update Hex.lean**

`bytesToHex` currently takes `ByteArray`. Two options:
- Change to take `List UInt8` and use `List.foldl`
- Or keep it taking `ByteArray` since `deployCode` still returns `ByteArray`

Prefer keeping `ByteArray` in Hex.lean since it's the output boundary. No change needed if `deployCode` still returns `Option ByteArray`.

**Step 3: Full build**

Run: `~/.elan/bin/lake build`
Expected: Full project builds. The `#eval` in Hex.lean still prints the same hex string.

**Step 4: Run E2E test**

```bash
bash test/evm_e2e.sh
```
Expected: All assertions pass. Same bytecode as before.

**Step 5: Commit**

```bash
jj commit -m "refactor(evm): update Contract/Hex for List UInt8 assembler"
```

---

## Task 3: Theorem 1 — Op.toBytes_length

**Files:**
- Create: `Lemma/EVM/Proofs/OpSize.lean`

**Step 1: Prove encoding length equals size**

```lean
import Lemma.EVM.Op

namespace EVM.Proofs

theorem Op.toBytes_length (o : EVM.Op) : o.toBytes.length = o.size := by
  cases o <;> simp [EVM.Op.toBytes, EVM.Op.size]
  -- push1 and push4 cases may need additional unfolding
```

This should close by case analysis on all 23 `Op` constructors. Each case is definitional — the `toBytes` output is a literal list whose length matches `size`.

If `simp` doesn't close all cases, try `decide` or manual `rfl` for stubborn cases. The `push4` case involves `let` bindings that may need unfolding.

**Step 2: Verify it compiles with no sorry**

Run: `~/.elan/bin/lake build Lemma.EVM.Proofs.OpSize`
Expected: Build succeeds, no sorry warnings.

**Step 3: Commit**

```bash
jj commit -m "proof(evm): Op.toBytes_length — encoding length matches size"
```

---

## Task 4: Theorem 2 — assemble_length

**Files:**
- Create: `Lemma/EVM/Proofs/AsmSize.lean`

**Step 1: Prove the accumulator lemma**

The key helper — relates `emit`'s accumulator to `asmSize`:

```lean
import Lemma.EVM.Asm
import Lemma.EVM.Proofs.OpSize

namespace EVM.Proofs

-- The emit loop preserves the length invariant
theorem emit_length (labels : List (String × Nat)) (items : List EVM.AsmItem)
    (acc : List UInt8) (result : List UInt8) :
    EVM.assemble.emit labels items acc = some result →
    result.length = acc.length + EVM.asmSize items
```

Proof: induction on `items`.
- Base case: `emit [] acc = some acc`, and `asmSize [] = 0`. Trivial.
- `.label _` case: `emit rest (acc ++ [0x5b])`. By IH, `result.length = (acc ++ [0x5b]).length + asmSize rest`. Since `(acc ++ [0x5b]).length = acc.length + 1` and `AsmItem.size (.label _) = 1`, this gives `acc.length + 1 + asmSize rest = acc.length + asmSize (label :: rest)`.
- `.op o` case: `emit rest (acc ++ o.toBytes)`. By IH + `Op.toBytes_length`, `(acc ++ o.toBytes).length = acc.length + o.size`.
- `.pushLabelRef name` case: if lookup succeeds, `emit rest (acc ++ [0x60, offset.toUInt8])`. Length increases by 2, which equals `AsmItem.size (.pushLabelRef _)`.

**Step 2: Prove the main theorem**

```lean
theorem assemble_length (items : List EVM.AsmItem) (bytes : List UInt8) :
    EVM.assemble items = some bytes → bytes.length = EVM.asmSize items
```

Unfold `assemble`, apply `emit_length` with `acc = []`.

**Step 3: Verify — no sorry**

Run: `~/.elan/bin/lake build Lemma.EVM.Proofs.AsmSize`

**Step 4: Commit**

```bash
jj commit -m "proof(evm): assemble_length — output size matches asmSize prediction"
```

---

## Task 5: Theorem 3 — resolveLabels_bound

**Files:**
- Create: `Lemma/EVM/Proofs/LabelBound.lean`

**Step 1: Prove helper about resolveLabels.go**

The `go` function accumulates `(name, offset)` pairs where `offset` is the running byte count. We need to show every recorded offset is less than the total `asmSize`.

```lean
import Lemma.EVM.Asm

namespace EVM.Proofs

-- Helper: offsets recorded by go are bounded
theorem resolveLabels_go_bound (items : List EVM.AsmItem) (offset : Nat)
    (acc : List (String × Nat)) (name : String) (off : Nat) :
    (EVM.resolveLabels.go items offset acc).lookup name = some off →
    -- Either it was already in acc, or it was added during traversal
    (acc.lookup name = some off) ∨ (off < offset + EVM.asmSize items)
```

**Step 2: Prove the main theorem**

```lean
theorem resolveLabels_bound (items : List EVM.AsmItem) (name : String) (offset : Nat) :
    (EVM.resolveLabels items).lookup name = some offset →
    offset < EVM.asmSize items
```

Unfold `resolveLabels` (which calls `go items 0 []`), apply the helper with empty initial acc.

Note: this requires that `asmSize items > 0` when any label exists, which is true since each label contributes 1 byte. If the list is empty, `resolveLabels` returns `[]` and lookup fails, so the premise is vacuously false.

**Step 3: Verify — no sorry**

Run: `~/.elan/bin/lake build Lemma.EVM.Proofs.LabelBound`

**Step 4: Commit**

```bash
jj commit -m "proof(evm): resolveLabels_bound — label offsets are within bounds"
```

---

## Task 6: Theorems 4-5 — Label Correctness

**Files:**
- Create: `Lemma/EVM/Proofs/LabelCorrect.lean`

This is the hardest task. Theorems 4 and 5 prove that `resolveLabels` and `emit` agree on positions.

**Step 1: Define the sync invariant**

The core insight: `resolveLabels.go` and `emit` traverse the same list, incrementing a byte offset by the same amount at each step. We formalize this as:

```lean
import Lemma.EVM.Asm
import Lemma.EVM.Proofs.OpSize
import Lemma.EVM.Proofs.AsmSize

namespace EVM.Proofs

-- Sync invariant: when emit processes items starting from accumulator `acc`,
-- and resolveLabels assigned offset `off` to label `name`,
-- then the byte at position `off` in the final output is 0x5b.
```

**Step 2: Prove Theorem 4 — label_points_to_jumpdest**

```lean
theorem label_points_to_jumpdest (items : List EVM.AsmItem) (bytes : List UInt8)
    (name : String) (offset : Nat) :
    EVM.assemble items = some bytes →
    (EVM.resolveLabels items).lookup name = some offset →
    bytes.get? offset = some 0x5b
```

The proof needs a stronger inductive hypothesis that tracks the relationship between the accumulator position in `emit` and the offset tracker in `resolveLabels.go`. The key lemma:

```lean
-- When emit produces output, bytes at label offsets are JUMPDEST
theorem emit_preserves_label_bytes (labels : List (String × Nat))
    (items : List EVM.AsmItem) (acc result : List UInt8)
    (name : String) (offset : Nat) :
    EVM.assemble.emit labels items acc = some result →
    -- The label was resolved to this offset
    labels.lookup name = some offset →
    -- The offset falls within the accumulator portion (already emitted)
    offset < acc.length →
    -- The byte is preserved
    result.get? offset = acc.get? offset
```

Plus a lemma for when the label is in the *remaining* items:

```lean
-- When emit reaches a label item, it places 0x5b at the current acc length
theorem emit_places_jumpdest (labels : List (String × Nat))
    (items : List EVM.AsmItem) (acc result : List UInt8) :
    EVM.assemble.emit labels (.label name :: items) acc = some result →
    result.get? acc.length = some 0x5b
```

The main theorem follows by combining: `resolveLabels` records offset = accumulated byte count when it sees `.label name`, and `emit` places `0x5b` at exactly that accumulated byte count.

**Step 3: Prove Theorem 5 — pushLabelRef_uses_resolved_offset**

```lean
theorem pushLabelRef_uses_resolved_offset (items : List EVM.AsmItem) (bytes : List UInt8)
    (name : String) (offset : Nat) (pos : Nat) :
    EVM.assemble items = some bytes →
    (EVM.resolveLabels items).lookup name = some offset →
    bytes.get? pos = some 0x60 →
    bytes.get? (pos + 1) = some offset.toUInt8
```

Similar structure to Theorem 4. When `emit` processes `.pushLabelRef name`, it appends `[0x60, offset.toUInt8]` where `offset` comes from `labels.lookup name`. Since `labels = resolveLabels items`, Theorem 4 guarantees this offset points to a JUMPDEST.

Note: Theorem 5's statement may need refinement during implementation. The `pos` parameter needs to be constrained to be the actual position where a `pushLabelRef` emits — otherwise the premise `bytes.get? pos = some 0x60` could match a 0x60 byte from a `push1 0x60` opcode. Consider whether we need a stronger statement that identifies `pos` structurally. If this becomes too complex, an acceptable fallback is proving the weaker statement about what `emit` produces for `pushLabelRef` items specifically (without the `pos` indirection).

**Step 4: Verify — no sorry**

Run: `~/.elan/bin/lake build Lemma.EVM.Proofs.LabelCorrect`

**Step 5: Commit**

```bash
jj commit -m "proof(evm): label correctness — JUMP targets land on JUMPDESTs"
```

---

## Task 7: Wire Up Imports and Full Verification

**Files:**
- Modify: `Lemma.lean` — add imports for all proof modules

**Step 1: Add imports**

Add to `Lemma.lean`:
```lean
import Lemma.EVM.Proofs.OpSize
import Lemma.EVM.Proofs.AsmSize
import Lemma.EVM.Proofs.LabelBound
import Lemma.EVM.Proofs.LabelCorrect
```

**Step 2: Full build**

Run: `~/.elan/bin/lake build`
Expected: Full project builds with no errors, no sorry warnings.

**Step 3: Run E2E test**

```bash
bash test/evm_e2e.sh
```
Expected: All assertions still pass.

**Step 4: Commit**

```bash
jj commit -m "feat(evm): wire up assembler proof imports"
```

---

## Task 8: Findings Doc

**Files:**
- Create: `docs/plans/2026-02-24-assembler-verification-findings.md`

Record:
- Which theorems were proved (all 5, or which subset if any needed sorry)
- Proof sizes (lines per theorem)
- Issues encountered during proving
- Kill criteria results table
- Refactoring impact (did the List UInt8 change cause issues?)
- Assessment: what this means for the trust chain
- Next steps toward Tier B (EVM execution semantics)

Follow the format from `docs/plans/2026-02-24-evm-codegen-findings.md`.

**Commit:**

```bash
jj commit -m "docs(sprint6): add findings — assembler verification"
```
