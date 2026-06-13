# lean-evm

A Lean 4 model of an EVM bytecode subset, codegen for an ERC-20 subset, and
machine-checked correctness proofs connecting deployed bytecode back to a
dependently-typed `Ledger` specification. Extracted from the `lemma` project.

## Build

```bash
~/.elan/bin/lake build          # lake is NOT on PATH
~/.elan/bin/lake build Module   # build a specific module
~/.elan/bin/lake exe cache get  # fetch prebuilt Mathlib oleans (run after `lake update`)
```

- Lean version: 4.29.0-rc1 (see `lean-toolchain`)
- Mathlib is a dependency, pinned in `lakefile.lean` to the rev matching the toolchain.
  Only `Lemma/Scaled/{Basic,Ledger}.lean` use it (the `Ledger` invariant + sum lemmas).
- Target: 0 sorry across all modules.

## Structure

- `Lemma/EVM/` — EVM semantics (`State`, `Decode`, `Step`, `Exec`), opcode model
  (`Op`), assembler (`Asm`), ABI/`Layout`, codegen (`Codegen/`), and correctness
  proofs (`Proofs/`).
- `Lemma/Scaled/` — the dependently-typed spec layer: `Ledger` (invariant
  `totalSupply = Σ balances` as a proof field), `Basic` (Fin n sum lemmas),
  `Atoms/` (transfer/mint/burn, return type *is* the spec), `Compose/` (four proved
  atom compositions), `GlueSpecs/` (extracted composition obligations), and
  `Tactic/ExtractGlueSpec.lean` (tactic that emits a composition's obligation as a stub).
- `docs/` — design/findings docs and `achievements.md`.
- `test/evm_e2e.sh` — Anvil end-to-end test (requires Foundry).

## Proof architecture

Each ERC-20 function (`totalSupply`, `balanceOf`, `mint`, `transfer`) is proved in 4 tiers:

1. **Execution core** (`*Correct.lean`) — phased `execute` on concrete bytecode,
   split at SHA3 boundaries and conditional branches.
2. **Assembly bridge** (`*Asm.lean`) — `assemble functionCode = some [bytes]` via `native_decide`.
3. **Dispatch routing** (`DispatchCorrect.lean`) — end-to-end from `runtimeCode` + selector.
4. **Ledger bridge** (`*_matches_ledger` in `*Correct.lean`) — bytecode storage
   mutations match the `Scaled.Ledger` postconditions exactly.

`keccak256` is `opaque` — proofs reason about it axiomatically (distinct inputs → distinct
outputs via hypotheses like `hne : hash(a) ≠ hash(b)`), never assuming hash internals.
