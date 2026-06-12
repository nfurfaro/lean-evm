# Sprint 6: Assembler Verification

**Date:** 2026-02-24
**Status:** Design
**Goal:** Formally prove that the EVM assembler's label resolution is consistent with its byte emission — every JUMP target lands on a JUMPDEST.

---

## Motivation

Sprint 5 built a working spec→bytecode pipeline. The assembler is the single bridge between semantic opcodes (`List AsmItem`) and raw bytes (`List UInt8`). It has two phases that must agree:

1. **`resolveLabels`** — traverses items left-to-right, computing byte offsets for each label
2. **`emit`** — traverses items left-to-right, emitting bytes and looking up label offsets

If these two traversals disagree, JUMP instructions land on wrong bytes — silently producing broken contracts. This is the highest-leverage verification target: a small proof surface (52 lines of assembler) that guards the entire codegen output.

---

## What We're Proving

Five theorems, building bottom-up:

### Level 1: Encoding Faithfulness

```lean
theorem Op.toBytes_length (o : Op) : o.toBytes.length = o.size
```

Each opcode's byte encoding is exactly as long as `size` predicts. Foundation for everything above.

**Proof strategy:** Exhaustive case split on all 23 `Op` constructors. Every case is definitional.

### Level 2: Assembly Size Consistency

```lean
theorem assemble_length (items : List AsmItem) (bytes : List UInt8) :
    assemble items = some bytes → bytes.length = asmSize items
```

The assembled output is exactly as long as `asmSize` predicts. This means size predictions used during label resolution are accurate.

**Proof strategy:** Induction on `items` with an accumulator invariant:
```lean
-- Helper: emit preserves the length relationship
emit items acc = some result → result.length = acc.length + asmSize items
```
The `.op` case uses Theorem 1. The `.pushLabelRef` case uses the fact that `assemble` returned `some` (so lookup succeeded).

### Level 3: Label Offset Bounds

```lean
theorem resolveLabels_bound (items : List AsmItem) (name : String) (offset : Nat) :
    (resolveLabels items).lookup name = some offset → offset < asmSize items
```

Every resolved offset is within the bounds of the assembled output. Prevents out-of-bounds jumps.

**Proof strategy:** Induction on the `go` helper in `resolveLabels`. The running offset accumulator is always ≤ `asmSize` of the full list. Labels record the current offset, which is strictly less than total size (since the label itself contributes 1 byte).

### Level 4: Label Points to JUMPDEST

```lean
theorem label_points_to_jumpdest (items : List AsmItem) (bytes : List UInt8)
    (name : String) (offset : Nat) :
    assemble items = some bytes →
    (resolveLabels items).lookup name = some offset →
    bytes.get? offset = some 0x5b
```

The byte at a resolved label offset is 0x5b (JUMPDEST). This is the core trust property — it guarantees JUMP targets are valid.

**Proof strategy:** The key insight is that `resolveLabels` and `emit` traverse the same list in the same order, accumulating the same byte offset. We prove they stay in sync via an inductive invariant:

> At each step, the accumulator length in `emit` equals the running offset in `resolveLabels`.

When `emit` reaches a `.label name`, it appends `[0x5b]` at exactly the position `resolveLabels` recorded for `name`. Therefore `bytes.get? offset = some 0x5b`.

### Level 5: Label Refs Use Correct Offset

```lean
theorem pushLabelRef_uses_resolved_offset (items : List AsmItem) (bytes : List UInt8)
    (name : String) (offset : Nat) (pos : Nat) :
    assemble items = some bytes →
    (resolveLabels items).lookup name = some offset →
    -- At byte position `pos` where the pushLabelRef emits:
    bytes.get? pos = some 0x60 →
    bytes.get? (pos + 1) = some offset.toUInt8
```

When `emit` processes a `pushLabelRef name`, it emits `[0x60, offset.toUInt8]` where `offset` is the resolved label position. Combined with Theorem 4, this means every label reference points to a JUMPDEST.

**Proof strategy:** Follows from the same sync invariant as Theorem 4. When `emit` reaches a `.pushLabelRef`, it calls `labels.lookup name`, gets `some offset`, and appends `[0x60, offset.toUInt8]`. The `offset` comes from the same `resolveLabels` call, so Theorem 4 guarantees it points to a JUMPDEST.

---

## Refactoring Plan

Minimal changes to make proofs tractable. `ByteArray` is extern-backed and hard to reason about; `List UInt8` has rich simp lemmas.

### Asm.lean

Change `assemble` to return `Option (List UInt8)`:

```lean
def assemble (items : List AsmItem) : Option (List UInt8) :=
  let labels := resolveLabels items
  let rec emit (items : List AsmItem) (acc : List UInt8) : Option (List UInt8) :=
    match items with
    | [] => some acc
    | item :: rest =>
      match item with
      | .label _ => emit rest (acc ++ [0x5b])
      | .op o => emit rest (acc ++ o.toBytes)
      | .pushLabelRef name =>
        match labels.lookup name with
        | some offset => emit rest (acc ++ [0x60, offset.toUInt8])
        | none => none
  emit items []

-- ByteArray wrapper for existing consumers
def assembleBytes (items : List AsmItem) : Option ByteArray :=
  (assemble items).map fun bs => ⟨bs.toArray⟩
```

Changes: `ByteArray.push` → `List.append`, return type `Option ByteArray` → `Option (List UInt8)`. Add `assembleBytes` wrapper.

### Contract.lean

Update `deployCode` to use `assemble` (now returns `List UInt8`):

```lean
def deployCode : Option ByteArray :=
  match assemble runtimeCode with
  | none => none
  | some runtimeBytes =>
    let runtimeSize := runtimeBytes.length.toUInt8
    -- ... preamble unchanged ...
    some ⟨(preamble ++ runtimeBytes).toArray⟩
```

### Hex.lean

Update `bytesToHex` to accept `List UInt8` or convert at boundary. Minimal change.

### Op.lean, Layout.lean, ABI.lean, Codegen/Mint.lean, Codegen/Getters.lean

No changes.

---

## File Structure

```
Lemma/EVM/
├── Op.lean                    -- unchanged
├── Asm.lean                   -- refactored: List UInt8
├── Layout.lean                -- unchanged
├── ABI.lean                   -- unchanged
├── Hex.lean                   -- updated for List UInt8
├── Codegen/
│   ├── Mint.lean              -- unchanged
│   ├── Getters.lean           -- unchanged
│   └── Contract.lean          -- updated for List UInt8
└── Proofs/
    ├── OpSize.lean            -- Theorem 1
    ├── AsmSize.lean           -- Theorem 2 + accumulator lemma
    ├── LabelBound.lean        -- Theorem 3
    └── LabelCorrect.lean      -- Theorems 4-5 + sync invariant
```

---

## Kill Criteria

| Criterion | How to verify |
|---|---|
| `lake build` succeeds with all proofs | No `sorry` in any proof file, full build passes |
| Theorem 1: encoding length = size | `Op.toBytes_length` proved for all 23 opcodes |
| Theorem 2: output length = asmSize | `assemble_length` proved |
| Theorem 3: offsets in bounds | `resolveLabels_bound` proved |
| Theorem 4: labels → JUMPDEST | `label_points_to_jumpdest` proved |
| Theorem 5: refs use correct offset | `pushLabelRef_uses_resolved_offset` proved |
| E2E test still passes | `bash test/evm_e2e.sh` green after refactoring |

---

## Out of Scope

- EVM execution semantics (`exec : EVMState → Op → EVMState`)
- Codegen correctness (proving `mintCode` matches the mint spec)
- Deployment preamble verification (bypasses `Op` type)
- Assembler-is-injective (different programs → different bytecode)
- New opcodes or optimizations

---

## What Success Proves

If all kill criteria pass, we've demonstrated that:
1. The assembler's two-phase architecture (resolve then emit) is internally consistent
2. Every JUMP target in the generated bytecode lands on a JUMPDEST
3. The first link in the spec→bytecode trust chain is formally verified
4. The Lean 4 proof infrastructure can reason about bytecode generation

This is the foundation for Tier B (EVM execution semantics) and Tier C (full codegen verification).
