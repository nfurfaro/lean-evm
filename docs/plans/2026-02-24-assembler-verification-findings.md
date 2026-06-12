# Sprint 6 Findings: Assembler Verification

**Date:** 2026-02-24
**Status:** Complete — all kill criteria PASS
**Lean version:** 4.29.0-rc1

---

## Summary

**The assembler is formally verified.** Five theorems proved with zero sorry, covering encoding faithfulness, size consistency, label offset bounds, label-to-JUMPDEST correctness, and pushLabelRef emission. The core trust property — every JUMP target lands on a JUMPDEST — is machine-checked. Total proof surface: 481 lines across 4 files.

---

## Kill Criterion Results

| Criterion | How to verify | Actual | Result |
|---|---|---|---|
| `lake build` succeeds with all proofs | No `sorry` in any proof file, full build passes | 993 build jobs, zero errors, zero sorry | **PASS** |
| Theorem 1: encoding length = size | `Op.toBytes_length` proved for all 23 opcodes | Proved by exhaustive case split, 14 lines | **PASS** |
| Theorem 2: output length = asmSize | `assemble_length` proved | Proved with accumulator invariant, 97 lines | **PASS** |
| Theorem 3: offsets in bounds | `resolveLabels_bound` proved | Proved via membership + go invariant, 114 lines | **PASS** |
| Theorem 4: labels → JUMPDEST | `label_points_to_jumpdest` proved | Proved via emit/go sync invariant, in LabelCorrect.lean | **PASS** |
| Theorem 5: refs use correct offset | `pushLabelRef_uses_resolved_offset` proved | Structural approach (prefix decomposition), in LabelCorrect.lean | **PASS** |
| E2E test still passes | `bash test/evm_e2e.sh` green after refactoring | 4/4 assertions pass | **PASS** |

---

## Proof Architecture

```
OpSize.lean         Theorem 1: Op.toBytes_length
    ↓
AsmSize.lean        Theorem 2: assemble_length (uses Theorem 1)
    ↓
LabelBound.lean     Theorem 3: resolveLabels_bound (uses asmSize_cons from AsmSize)
    ↓
LabelCorrect.lean   Theorems 4-5: label_points_to_jumpdest + pushLabelRef_uses_resolved_offset
```

Each proof module builds on the previous. The dependency chain is linear and minimal.

---

## Proof Sizes

| File | Theorem(s) | Lines | Key technique |
|---|---|---|---|
| `OpSize.lean` | `Op.toBytes_length` | 14 | Exhaustive case split + simp |
| `AsmSize.lean` | `emit_length`, `assemble_length` | 97 | Induction on items with accumulator invariant |
| `LabelBound.lean` | `go_mem_bound`, `resolveLabels_bound` | 114 | Membership-based invariant (avoids reverse complications) |
| `LabelCorrect.lean` | `label_points_to_jumpdest`, `pushLabelRef_uses_resolved_offset` | 256 | Emit/go sync invariant + prefix preservation |
| **Total** | **5 theorems + helpers** | **481** | |

LabelCorrect.lean is the largest file (256 lines) because it requires three helper lemmas:
1. `emit_preserves_prefix` — emit only appends, never modifies existing bytes
2. `emit_go_label_sync` — the core sync between resolveLabels.go and emit
3. `emit_pushLabelRef_bytes` — structural lemma for pushLabelRef emission

---

## Refactoring Impact

The `List UInt8` refactoring (Tasks 1-2) was essential. The original `ByteArray` accumulator would have been impossible to reason about — `ByteArray` is extern-backed with no simp lemmas. `List UInt8` provides:
- `List.length_append` for length reasoning
- `List.getElem?_append_left/right` for index-based access
- Standard induction principles

The refactoring was clean: only `Asm.lean`, `Contract.lean` needed changes. The `assembleBytes` wrapper preserved the `ByteArray` interface for consumers. E2E test passed immediately after refactoring.

---

## Issues Encountered

| Issue | Cause | Resolution |
|---|---|---|
| `emit` captured as `let rec` | `emit` inside `assemble` lifts to `EVM.assemble.emit` with `labels` as explicit first param | Used `EVM.assemble.emit labels items acc` in all proof statements |
| `resolveLabels.go` returns `acc.reverse` | Lookup order differs from insertion order | Worked with membership (`∈`) instead of `List.lookup` for go invariants, then bridged via `lookup_some_mem` |
| Theorem 5 statement fragility | Bare `bytes.get? pos = some 0x60` could match any PUSH1 opcode | Redesigned with structural approach: caller provides `items = pre ++ .pushLabelRef name :: suf` |
| `List.get?` vs `getElem?` notation | Lean 4.29 prefers bracket notation `xs[i]?` | Used `[i]?` throughout; definitionally equal to `get?` |
| `dsimp` needed for match reduction | After `unfold EVM.assemble.emit` + `cases item`, pushLabelRef match not auto-reduced | `dsimp at h_emit` cleanly reduces iota-redexes |

None of these were blockers. The membership approach for `go` invariants is a reusable pattern.

---

## Assessment

### What the proofs establish

The five theorems together guarantee:

1. **Encoding faithfulness** (Theorem 1): Each opcode serializes to exactly `size` bytes.
2. **Size prediction accuracy** (Theorem 2): `asmSize` correctly predicts assembled output length.
3. **Offset safety** (Theorem 3): Every resolved label offset is within bounds.
4. **JUMPDEST correctness** (Theorem 4): Every resolved label points to a `0x5b` byte.
5. **Reference correctness** (Theorem 5): Every `pushLabelRef` emits `PUSH1` + the correct resolved offset.

Combined, Theorems 4 and 5 prove: **every JUMP in the generated bytecode targets a valid JUMPDEST.** This is the core safety property for the assembler — without it, the EVM would reject the bytecode at runtime.

### What the proofs do NOT establish

- **EVM execution semantics**: We don't model what opcodes *do*, only that labels resolve correctly.
- **Codegen correctness**: We don't prove that `mintCode` matches the mint spec.
- **Deploy preamble**: The raw-byte preamble in `Contract.lean` is not verified.
- **Assembler injectivity**: Different programs could theoretically produce the same bytecode.

### Trust chain status

```
spec mint ...  →  macro  →  verified atom  →  codegen  →  assembler  →  EVM bytecode
                                               unverified    VERIFIED     runtime
```

The assembler link is now formally verified. The remaining unverified links are:
- **Codegen → assembler**: proving `mintCode` opcodes match mint spec postconditions
- **Deploy preamble**: routing through `Op` type or proving correctness of raw bytes

---

## Deliverables

| Deliverable | Location |
|---|---|
| Theorem 1: Op.toBytes_length | `Lemma/EVM/Proofs/OpSize.lean` |
| Theorem 2: assemble_length | `Lemma/EVM/Proofs/AsmSize.lean` |
| Theorem 3: resolveLabels_bound | `Lemma/EVM/Proofs/LabelBound.lean` |
| Theorems 4-5: label correctness | `Lemma/EVM/Proofs/LabelCorrect.lean` |
| Proof imports wired up | `Lemma.lean` |
| Design doc | `docs/plans/2026-02-24-assembler-verification-design.md` |
| Implementation plan | `docs/plans/2026-02-24-assembler-verification-plan.md` |
| This findings doc | `docs/plans/2026-02-24-assembler-verification-findings.md` |

8 commits on main for Sprint 6. No new dependencies added.

---

## Conclusions

### Lean 4 can verify bytecode generation infrastructure.

481 lines of proof verify 56 lines of assembler. The proof-to-code ratio (~8.5:1) is high but expected for the core trust property. Future proofs building on these lemmas will amortize the investment.

### The membership-over-lookup pattern is essential.

`resolveLabels.go` returns `acc.reverse`, making direct `List.lookup` reasoning on intermediate states intractable. Working with `∈` (membership) and bridging to `lookup` only at the top level is the right pattern. This applies to any accumulator-reversing function.

### The assembler's two-phase design is provably correct.

`resolveLabels` and `emit` traverse the same list computing the same byte offsets. The sync invariant (`emit_go_label_sync`) formalizes this and can be reused if the assembler is extended with new item types.

---

## Next Steps

1. **Tier B: EVM execution semantics** — define `exec : EVMState → Op → EVMState` and prove that `mintCode` produces state transitions matching the mint spec's postconditions
2. **Deploy preamble verification** — route preamble through `Op` type to bring it under the verified assembler
3. **PUSH2 support** — extend assembler for contracts > 255 bytes, with updated bounds proofs
4. **Additional atom codegen** — extend codegen to burn and transfer, reusing the verified assembler
