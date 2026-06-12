import Lemma.EVM.Exec
import Lemma.EVM.Proofs.MintAsm
import Lemma.EVM.Proofs.BalanceOfCorrect
import Lemma.Scaled.Ledger

/-!
# mint Correctness Proof

Proves that executing the assembled `mintCode` bytecode correctly
updates storage: `balances[dst] += amt` and `totalSupply += amt`.

## Execution trace (26 steps on 35 bytes)

| Step | PC | Instr          | Stack                              | Side effects          |
|------|----|----------------|------------------------------------|-----------------------|
| 0    | 0  | PUSH1 0x04     | [] → [4]                           |                       |
| 1    | 2  | CALLDATALOAD   | [4] → [dst]                        |                       |
| 2    | 3  | PUSH1 0x24     | [dst] → [36,dst]                   |                       |
| 3    | 5  | CALLDATALOAD   | [36,dst] → [amt,dst]               |                       |
| 4    | 6  | DUP2           | → [dst,amt,dst]                    |                       |
| 5    | 7  | PUSH1 0x00     | → [0,dst,amt,dst]                  |                       |
| 6    | 9  | MSTORE         | → [amt,dst]                        | mem[0]:=dst           |
| 7    | 10 | PUSH1 0x01     | → [1,amt,dst]                      |                       |
| 8    | 12 | PUSH1 0x20     | → [32,1,amt,dst]                   |                       |
| 9    | 14 | MSTORE         | → [amt,dst]                        | mem[1]:=1             |
| 10   | 15 | PUSH1 0x40     | → [64,amt,dst]                     |                       |
| 11   | 17 | PUSH1 0x00     | → [0,64,amt,dst]                   |                       |
| 12   | 19 | SHA3           | → [slot,amt,dst]                   |                       |
| 13   | 20 | DUP1           | → [slot,slot,amt,dst]              |                       |
| 14   | 21 | SLOAD          | → [bal,slot,amt,dst]               |                       |
| 15   | 22 | DUP3           | → [amt,bal,slot,amt,dst]           |                       |
| 16   | 23 | ADD            | → [bal+amt,slot,amt,dst]           |                       |
| 17   | 24 | SWAP1          | → [slot,bal+amt,amt,dst]           |                       |
| 18   | 25 | SSTORE         | → [amt,dst]                        | sto[slot]:=bal+amt    |
| 19   | 26 | PUSH1 0x00     | → [0,amt,dst]                      |                       |
| 20   | 28 | SLOAD          | → [supply,amt,dst]                 |                       |
| 21   | 29 | ADD            | → [supply+amt,dst]                 |                       |
| 22   | 30 | PUSH1 0x00     | → [0,supply+amt,dst]               |                       |
| 23   | 32 | SSTORE         | → [dst]                            | sto[0]:=supply+amt    |
| 24   | 33 | POP            | → []                               |                       |
| 25   | 34 | STOP           | halt                               |                       |

Requires hypothesis `bal_slot ≠ 0` so that SLOAD at step 20 reads the
original totalSupply (not the just-written balance).
-/

namespace EVM

private def mCode : List UInt8 :=
  [0x60, 0x04, 0x35, 0x60, 0x24, 0x35, 0x81, 0x60, 0x00, 0x52,
   0x60, 0x01, 0x60, 0x20, 0x52, 0x60, 0x40, 0x60, 0x00, 0x20,
   0x80, 0x54, 0x82, 0x01, 0x90, 0x55, 0x60, 0x00, 0x54, 0x01,
   0x60, 0x00, 0x55, 0x50, 0x00]

-- ───────────────────── Memory helpers ──────────────────────

-- Reuse the two-word memory result from BalanceOfCorrect
theorem extractMemBytes_two_words' (dst : Word) :
    extractMemBytes (writeMem (writeMem Memory.default 0 dst) 32 1) 0 64
    = wordToBytes dst ++ wordToBytes 1 :=
  extractMemBytes_two_words dst

-- ───────────────────── Execution phasing ──────────────────────

set_option maxHeartbeats 800000 in
private theorem mint_exec_phase1 (storage : Nat → Word) (calldata : List UInt8) :
    execute mCode { State.init storage with calldata := calldata } 27 =
    execute mCode
      { pc := 20
        stack := [keccak256 (extractMemBytes
          (writeMem (writeMem Memory.default 0 (calldataWord calldata 4)) 32 1) 0 64),
          calldataWord calldata 0x24, calldataWord calldata 4]
        memory := writeMem (writeMem Memory.default 0 (calldataWord calldata 4)) 32 1
        storage := storage
        calldata := calldata } 14 := by
  rfl

/-- Phase 2: Steps 13–18 (balance SLOAD + SSTORE). -/
private theorem mint_exec_phase2 (storage : Nat → Word) (calldata : List UInt8)
    (bal_slot amt dst : Nat) (mem : Nat → Bytes32) :
    execute mCode
      { pc := 20, stack := [bal_slot, amt, dst],
        memory := mem, storage := storage, calldata := calldata } 14 =
    execute mCode
      { pc := 26
        stack := [amt, dst]
        memory := mem
        storage := fun k => if k = bal_slot then amt + storage bal_slot else storage k
        calldata := calldata } 8 := by
  rfl

/-- Phase 3: Steps 19–25 (totalSupply SLOAD + SSTORE + POP + STOP).
    Generalized over the full storage function. -/
private theorem mint_exec_phase3 (sto : Nat → Word) (calldata : List UInt8)
    (amt dst : Nat) (mem : Nat → Bytes32) :
    execute mCode
      { pc := 26, stack := [amt, dst],
        memory := mem, storage := sto, calldata := calldata } 8 =
    .done
      { pc := 34, stack := [],
        memory := mem,
        storage := fun k => if k = 0 then sto 0 + amt else sto k,
        calldata := calldata } := by
  rfl

-- ───────────────────── Main theorems ──────────────────────

/-- Core theorem: executing the mint bytecode updates storage correctly.
    - `storage[keccak256(wordToBytes dst ++ wordToBytes 1)] += amt`
    - `storage[0] += amt` -/
theorem mint_correct (storage : Nat → Word) (calldata : List UInt8)
    (dst amt : Nat)
    (hdst : calldataWord calldata 4 = dst)
    (hamt : calldataWord calldata 0x24 = amt)
    (hne : keccak256 (wordToBytes dst ++ wordToBytes 1) ≠ 0) :
    ∃ s', execute mCode { State.init storage with calldata := calldata } 27
      = .done s'
    ∧ s'.storage (keccak256 (wordToBytes dst ++ wordToBytes 1))
        = storage (keccak256 (wordToBytes dst ++ wordToBytes 1)) + amt
    ∧ s'.storage 0 = storage 0 + amt := by
  subst hdst; subst hamt
  rw [mint_exec_phase1, extractMemBytes_two_words', mint_exec_phase2, mint_exec_phase3]
  refine ⟨_, rfl, ?_, ?_⟩
  · -- balance slot: reduces to a + b = b + a after if-elimination
    simp [hne, Nat.add_comm]
  · -- totalSupply slot: resolve inner if 0 = keccak256(...) with Ne.symm hne
    simp [Ne.symm hne]

/-- Codegen corollary: connects to the `assemble` function. -/
theorem mint_codegen_correct (storage : Nat → Word) (calldata : List UInt8)
    (code : List UInt8) (hasm : assemble Codegen.mintCode = some code)
    (dst amt : Nat)
    (hdst : calldataWord calldata 4 = dst)
    (hamt : calldataWord calldata 0x24 = amt)
    (hne : keccak256 (wordToBytes dst ++ wordToBytes 1) ≠ 0) :
    ∃ s', execute code { State.init storage with calldata := calldata } 27
      = .done s'
    ∧ s'.storage (keccak256 (wordToBytes dst ++ wordToBytes 1))
        = storage (keccak256 (wordToBytes dst ++ wordToBytes 1)) + amt
    ∧ s'.storage 0 = storage 0 + amt := by
  rw [mint_asm] at hasm
  injection hasm with hcode
  subst hcode
  exact mint_correct storage calldata _ _ hdst hamt hne

/-- Ledger bridge: connects EVM execution result back to `Scaled.Ledger.mint`.
    After executing mint bytecode, storage reflects the ledger's mint operation. -/
theorem mint_matches_ledger {n : Nat} [NeZero n] (l : Scaled.Ledger n)
    (calldata : List UInt8) (who : Fin n) (amt : Nat)
    (hdst : calldataWord calldata 4 = who.val)
    (hamt : calldataWord calldata 0x24 = amt)
    (storageSlot : Nat → Word)
    (hbal : storageSlot (keccak256 (wordToBytes who.val ++ wordToBytes 1)) = l.balances who)
    (hsup : storageSlot 0 = l.totalSupply)
    (hne : keccak256 (wordToBytes who.val ++ wordToBytes 1) ≠ 0) :
    ∃ s', execute mCode
      { State.init storageSlot with calldata := calldata } 27
      = .done s'
    ∧ s'.storage (keccak256 (wordToBytes who.val ++ wordToBytes 1))
        = l.balances who + amt
    ∧ s'.storage 0 = l.totalSupply + amt := by
  have ⟨s', hexec, hbal', hsup'⟩ := mint_correct storageSlot calldata _ _ hdst hamt hne
  exact ⟨s', hexec, by rw [hbal', hbal], by rw [hsup', hsup]⟩

end EVM
