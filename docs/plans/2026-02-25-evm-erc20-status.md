# EVM ERC-20: Status & Roadmap

**Date:** 2026-02-25
**Lean version:** 4.29.0-rc1
**Build:** 995 jobs, 0 sorry

---

## What's Done

### Sprints 5–6: Codegen + Proofs

| Component | Files | Status |
|---|---|---|
| EVM semantics | State, Step, Exec, Decode, Op (27 opcodes) | Complete |
| Assembler | Asm (two-pass, label resolution) | Complete |
| ABI / Layout | Selectors, calldata offsets, storage slots 0–1 | Complete |
| **totalSupply** codegen | Codegen/Getters.lean | Complete |
| **balanceOf** codegen | Codegen/Getters.lean | Complete |
| **mint** codegen | Codegen/Mint.lean | Complete |
| **transfer** codegen | Codegen/Transfer.lean | Complete |
| Dispatch + deploy | Codegen/Contract.lean (runtimeCode, deployCode) | Complete |
| Hex output | Hex.lean (197-byte deploy, tested on anvil) | Complete |

### Proofs

| Proof | File | Status |
|---|---|---|
| totalSupply execution correctness | Proofs/TotalSupplyCorrect.lean | 0 sorry |
| balanceOf execution correctness | Proofs/BalanceOfCorrect.lean | 0 sorry |
| mint execution correctness | Proofs/MintCorrect.lean | 0 sorry |
| totalSupply assembly | Proofs/TotalSupplyAsm.lean | 0 sorry |
| balanceOf assembly | Proofs/BalanceOfAsm.lean | 0 sorry |
| mint assembly | Proofs/MintAsm.lean | 0 sorry |
| Assembler infra (OpSize, AsmSize, LabelBound, LabelCorrect) | Proofs/*.lean | 0 sorry |
| Runtime assembly | Proofs/RuntimeAsm.lean | 0 sorry |
| transfer execution correctness | Proofs/TransferCorrect.lean | 0 sorry |
| transfer assembly | Proofs/TransferAsm.lean | 0 sorry |
| **Dispatch correctness** (all 4 functions) | Proofs/DispatchCorrect.lean | 0 sorry |

### Proof Architecture

Each function has four tiers:
1. **Execution core** — `execute` on concrete bytecode, phased at SHA3 boundary
2. **Assembly bridge** — `assemble functionCode = some [bytes]` via `native_decide`
3. **Codegen corollary** — connects execution proof to `Codegen.xxxCode`
4. **Dispatch routing** — end-to-end from `runtimeCode` with selector to function result

Key technique: phased execution splits at opaque `keccak256` boundaries. `selector_extract` is generic over fuel (`fuel + 4` not `4 + fuel` — Lean's `Nat.add` pattern-matches on second arg).

---

## What's Missing

### Functions

| Function | Codegen | Proof | Opcodes needed | Priority |
|---|---|---|---|---|
| ~~transfer(address, uint256)~~ | **Done** | **Done** | — | **Done** |
| **burn(address, uint256)** | Missing | Missing | SUB, LT, CALLER (have) | **High** |
| approve(address, uint256) | Missing | Missing | CALLER, allowances slot | Low |
| allowance(address, address) | Missing | Missing | Double-mapping hash | Low |
| transferFrom(address, address, uint256) | Missing | Missing | CALLER, SUB, LT, allowances | Low |

### Opcodes

| Opcode | Byte | Needed for | Effort |
|---|---|---|---|
| ~~SUB~~ | 0x03 | — | **Done** |
| ~~LT~~ | 0x10 | — | **Done** |
| ~~CALLER~~ | 0x33 | — | **Done** |
| ~~ISZERO~~ | 0x15 | — | **Done** |
| LOG0–LOG4 | 0xa0–0xa4 | ERC-20 Transfer/Approval events | Medium — 5 opcodes + event model |

### Infrastructure

| Item | Status | Priority |
|---|---|---|
| ~~`State.caller` field~~ | **Done** — `caller : Word := 0` on State | **Done** |
| `Layout.allowancesMappingSlot` | Missing — slot 2 for approve/allowance | Low |
| deployCode correctness proof | Missing — defined but unverified | Low |
| Deploy preamble via Op type | Raw bytes, bypasses assembler | Low |
| 256-bit Word overflow | Word := Nat (unbounded) | Low for PoC |

### Scaled Atoms Already Proved

These specs exist and are fully proved at the `Scaled` level — the EVM work connects bytecode back to them:

| Atom | File | Postconditions |
|---|---|---|
| transfer | Scaled/Atoms/Transfer.lean | src ≠ dst, amt ≤ bal[src], totalSupply preserved |
| mint | Scaled/Atoms/Mint.lean | bal[dst] += amt, totalSupply += amt |
| burn | Scaled/Atoms/Burn.lean | amt ≤ bal[src], bal[src] -= amt, totalSupply -= amt |

---

## Done: transfer (all 9 tasks complete)

All work items completed. EVM bytecode connects to the already-proved Scaled transfer atom.

### Work Items

1. ~~**Add opcodes**~~ — SUB, LT, ISZERO, CALLER added to Op.lean + Decode.lean + Step.lean
2. ~~**Add State.caller**~~ — `caller : Word := 0` field, threaded through all proofs
3. ~~**Write transferCode**~~ — Codegen/Transfer.lean (60-byte function body)
4. ~~**Assembly proof**~~ — TransferAsm.lean via `native_decide`
5. ~~**Execution proof**~~ — TransferCorrect.lean, phased: success path + revert path + totalSupply preservation
6. ~~**Wire into dispatch**~~ — selector 0xa9059cbb in Contract.lean runtimeCode (185-byte runtime)
7. ~~**Update DispatchCorrect**~~ — `runtime_transfer_correct` + all 4 selectors with caller threading
8. ~~**Ledger bridge**~~ — `transfer_matches_ledger` connects to Scaled.Atoms.Transfer postconditions
9. ~~**Test on anvil**~~ — deployed 197-byte contract, all tests pass (see below)

### Anvil Test Results

| Test | Expected | Actual | Status |
|---|---|---|---|
| mint(ACCT0, 1000) | success | success | PASS |
| totalSupply() | 1000 | 1000 | PASS |
| balanceOf(ACCT0) | 1000 | 1000 | PASS |
| transfer(ACCT0→ACCT1, 300) | success | success | PASS |
| balanceOf(ACCT0) after | 700 | 700 | PASS |
| balanceOf(ACCT1) after | 300 | 300 | PASS |
| totalSupply() preserved | 1000 | 1000 | PASS |
| transfer(ACCT0→ACCT1, 400) | success | success | PASS |
| balanceOf(ACCT0) after | 300 | 300 | PASS |
| balanceOf(ACCT1) after | 700 | 700 | PASS |
| transfer(9999, exceeds balance) | revert | revert | PASS |
| balances unchanged after revert | 300/700 | 300/700 | PASS |
| transfer(0 tokens) | success | success | PASS |
| transfer from ACCT1 (non-deployer) | success | success | PASS |
| final: ACCT0=500, ACCT1=500 | 500/500 | 500/500 | PASS |

### Key Discoveries

- `runtime_transfer_correct` requires `hne_src`/`hne_dst` hypotheses (keccak hash slots ≠ 0) for totalSupply preservation — matches mint's `hne` pattern
- `selector_extract` generalized with `(caller : Word)` — all dispatch theorems now thread caller
- balanceOf fuel 35→40 (extra selector check in dispatch for transfer)
- `extractMem_src`, `mem_overwrite`, `extractMem_dst` made non-private (needed by DispatchCorrect)

---

## Next: burn

The next highest-value function. All opcodes already exist (SUB, LT, CALLER, ISZERO). Pattern mirrors transfer but simpler (one storage update instead of two).
