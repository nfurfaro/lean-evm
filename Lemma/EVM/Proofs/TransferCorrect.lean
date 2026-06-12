import Lemma.EVM.Exec
import Lemma.EVM.Proofs.TransferAsm
import Lemma.EVM.Proofs.BalanceOfCorrect

/-!
# transfer Correctness Proof

Proves that executing the assembled `transferCode` bytecode correctly
updates storage: `balances[src] -= amt` and `balances[dst] += amt`,
provided `balances[src] >= amt`.

Two execution paths:
- **Success** (amt ≤ balances[src]): updates both balance slots, halts with STOP
- **Revert** (amt > balances[src]): halts with REVERT

The proof is phased at SHA3 boundaries and the conditional branch.
Phase 2 is split at the LT instruction because it introduces an `if`
on abstract values that requires a hypothesis to resolve.
-/

namespace EVM

private def tCode : List UInt8 :=
  [0x33, 0x60, 0x04, 0x35, 0x60, 0x24, 0x35, 0x82, 0x60, 0x00,
   0x52, 0x60, 0x01, 0x60, 0x20, 0x52, 0x60, 0x40, 0x60, 0x00,
   0x20, 0x80, 0x54, 0x82, 0x81, 0x10, 0x15, 0x60, 0x23, 0x57,
   0x60, 0x00, 0x60, 0x00, 0xfd, 0x5b, 0x82, 0x90, 0x03, 0x90,
   0x55, 0x81, 0x60, 0x00, 0x52, 0x60, 0x40, 0x60, 0x00, 0x20,
   0x80, 0x54, 0x82, 0x01, 0x90, 0x55, 0x50, 0x50, 0x50, 0x00]

-- ═══════════════════════════════════════════════════════════════
-- Phase 1: Load args + compute src_slot (14 steps, PC 0→21)
-- ═══════════════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
private theorem transfer_phase1 (storage : Nat → Word) (calldata : List UInt8) (caller : Word) :
    execute tCode { State.init storage with calldata := calldata, caller := caller } 46 =
    execute tCode
      { pc := 21
        stack := [keccak256 (extractMemBytes
          (writeMem (writeMem Memory.default 0 caller) 32 1) 0 64),
          calldataWord calldata 0x24, calldataWord calldata 4, caller]
        memory := writeMem (writeMem Memory.default 0 caller) 32 1
        storage := storage
        calldata := calldata
        caller := caller } 32 := by
  rfl

-- ═══════════════════════════════════════════════════════════════
-- Phase 2a: DUP1 + SLOAD + DUP3 + DUP2 + LT (5 steps, PC 21→26)
-- Produces `if storage src_slot < amt then 1 else 0` on stack.
-- ═══════════════════════════════════════════════════════════════

private theorem transfer_phase2a
    (storage : Nat → Word) (calldata : List UInt8) (caller : Word)
    (src_slot amt dst src : Nat) (mem : Nat → Bytes32) :
    execute tCode
      { pc := 21, stack := [src_slot, amt, dst, src],
        memory := mem, storage := storage, calldata := calldata, caller := caller } 32 =
    execute tCode
      { pc := 26
        stack := [if storage src_slot < amt then 1 else 0,
                  storage src_slot, src_slot, amt, dst, src]
        memory := mem
        storage := storage
        calldata := calldata
        caller := caller } 27 := by
  rfl

-- ═══════════════════════════════════════════════════════════════
-- Phase 2b (success): ISZERO + PUSH + JUMPI + JUMPDEST (4 steps, PC 26→36)
-- After resolving `if` to 0 (balance sufficient).
-- ═══════════════════════════════════════════════════════════════

private theorem transfer_phase2b_success
    (storage : Nat → Word) (calldata : List UInt8) (caller : Word)
    (src_bal src_slot amt dst src : Nat) (mem : Nat → Bytes32) :
    execute tCode
      { pc := 26, stack := [0, src_bal, src_slot, amt, dst, src],
        memory := mem, storage := storage, calldata := calldata, caller := caller } 27 =
    execute tCode
      { pc := 36
        stack := [src_bal, src_slot, amt, dst, src]
        memory := mem
        storage := storage
        calldata := calldata
        caller := caller } 23 := by
  rfl

-- ═══════════════════════════════════════════════════════════════
-- Phase 2b (revert): ISZERO + PUSH + JUMPI + PUSH + PUSH + REVERT
-- After resolving `if` to 1 (balance insufficient).
-- ═══════════════════════════════════════════════════════════════

private theorem transfer_phase2b_revert
    (storage : Nat → Word) (calldata : List UInt8) (caller : Word)
    (src_bal src_slot amt dst src : Nat) (mem : Nat → Bytes32) :
    execute tCode
      { pc := 26, stack := [1, src_bal, src_slot, amt, dst, src],
        memory := mem, storage := storage, calldata := calldata, caller := caller } 27 =
    .reverted := by
  rfl

-- ═══════════════════════════════════════════════════════════════
-- Phase 3: Update src balance (5 steps, PC 36→41)
-- ═══════════════════════════════════════════════════════════════

private theorem transfer_phase3
    (storage : Nat → Word) (calldata : List UInt8) (caller : Word)
    (src_bal src_slot amt dst src : Nat) (mem : Nat → Bytes32) :
    execute tCode
      { pc := 36
        stack := [src_bal, src_slot, amt, dst, src]
        memory := mem, storage := storage, calldata := calldata, caller := caller } 23 =
    execute tCode
      { pc := 41
        stack := [amt, dst, src]
        memory := mem
        storage := fun k => if k = src_slot then src_bal - amt else storage k
        calldata := calldata
        caller := caller } 18 := by
  rfl

-- ═══════════════════════════════════════════════════════════════
-- Phase 4: Compute dst_slot (6 steps, PC 41→50, through SHA3)
-- ═══════════════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
private theorem transfer_phase4
    (sto : Nat → Word) (calldata : List UInt8) (caller : Word)
    (amt dst src : Nat) (mem : Nat → Bytes32) :
    execute tCode
      { pc := 41, stack := [amt, dst, src],
        memory := mem, storage := sto, calldata := calldata, caller := caller } 18 =
    execute tCode
      { pc := 50
        stack := [keccak256 (extractMemBytes (writeMem mem 0 dst) 0 64),
                  amt, dst, src]
        memory := writeMem mem 0 dst
        storage := sto
        calldata := calldata
        caller := caller } 12 := by
  rfl

-- ═══════════════════════════════════════════════════════════════
-- Phase 5: Update dst balance + cleanup (10 steps, PC 50→halt)
-- ═══════════════════════════════════════════════════════════════

private theorem transfer_phase5
    (sto : Nat → Word) (calldata : List UInt8) (caller : Word)
    (dst_slot amt dst src : Nat) (mem : Nat → Bytes32) :
    execute tCode
      { pc := 50, stack := [dst_slot, amt, dst, src],
        memory := mem, storage := sto, calldata := calldata, caller := caller } 12 =
    .done
      { pc := 59, stack := []
        memory := mem
        storage := fun k => if k = dst_slot then amt + sto dst_slot else sto k
        calldata := calldata
        caller := caller } := by
  rfl

-- ═══════════════════════════════════════════════════════════════
-- Memory helpers
-- ═══════════════════════════════════════════════════════════════

theorem extractMem_src (src : Word) :
    extractMemBytes (writeMem (writeMem Memory.default 0 src) 32 1) 0 64
    = wordToBytes src ++ wordToBytes 1 :=
  extractMemBytes_two_words src

/-- After overwriting mem[0] with dst (where mem already has slot 1 = 1),
    extracting 64 bytes gives wordToBytes dst ++ wordToBytes 1. -/
theorem mem_overwrite (caller dst : Word) :
    writeMem (writeMem (writeMem Memory.default 0 caller) 32 1) 0 dst
    = writeMem (writeMem Memory.default 0 dst) 32 1 := by
  funext idx; simp [writeMem]; split <;> simp_all

theorem extractMem_dst (caller dst : Word) :
    extractMemBytes (writeMem (writeMem (writeMem Memory.default 0 caller) 32 1) 0 dst) 0 64
    = wordToBytes dst ++ wordToBytes 1 := by
  rw [mem_overwrite]; exact extractMemBytes_two_words dst

-- ═══════════════════════════════════════════════════════════════
-- Main theorems
-- ═══════════════════════════════════════════════════════════════

/-- Core theorem: executing the transfer bytecode updates storage correctly (success path).
    - `storage[src_slot] -= amt`
    - `storage[dst_slot] += amt`
    - `storage[0]` (totalSupply) is unchanged
    where src_slot = keccak256(wordToBytes caller ++ wordToBytes 1)
      and dst_slot = keccak256(wordToBytes dst ++ wordToBytes 1). -/
theorem transfer_correct (storage : Nat → Word) (calldata : List UInt8)
    (caller dst amt : Nat)
    (hdst : calldataWord calldata 4 = dst)
    (hamt : calldataWord calldata 0x24 = amt)
    (hbal : amt ≤ storage (keccak256 (wordToBytes caller ++ wordToBytes 1)))
    (hne : keccak256 (wordToBytes caller ++ wordToBytes 1) ≠
           keccak256 (wordToBytes dst ++ wordToBytes 1))
    (hne_src : keccak256 (wordToBytes caller ++ wordToBytes 1) ≠ 0)
    (hne_dst : keccak256 (wordToBytes dst ++ wordToBytes 1) ≠ 0) :
    let src_slot := keccak256 (wordToBytes caller ++ wordToBytes 1)
    let dst_slot := keccak256 (wordToBytes dst ++ wordToBytes 1)
    ∃ s', execute tCode { State.init storage with calldata := calldata, caller := caller } 46
      = .done s'
    ∧ s'.storage src_slot = storage src_slot - amt
    ∧ s'.storage dst_slot = storage dst_slot + amt
    ∧ s'.storage 0 = storage 0 := by
  subst hdst; subst hamt
  rw [transfer_phase1, extractMem_src, transfer_phase2a]
  have hlt : ¬ storage (keccak256 (wordToBytes caller ++ wordToBytes 1)) <
             calldataWord calldata 36 := not_lt.mpr hbal
  simp only [if_neg hlt]
  rw [transfer_phase2b_success, transfer_phase3, transfer_phase4,
      extractMem_dst, transfer_phase5]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp [hne]
  · simp [Ne.symm hne, Nat.add_comm]
  · simp [Ne.symm hne_dst, Ne.symm hne_src]

/-- Codegen corollary: connects to the `assemble` function. -/
theorem transfer_codegen_correct (storage : Nat → Word) (calldata : List UInt8)
    (code : List UInt8) (hasm : assemble Codegen.transferCode = some code)
    (caller dst amt : Nat)
    (hdst : calldataWord calldata 4 = dst)
    (hamt : calldataWord calldata 0x24 = amt)
    (hbal : amt ≤ storage (keccak256 (wordToBytes caller ++ wordToBytes 1)))
    (hne : keccak256 (wordToBytes caller ++ wordToBytes 1) ≠
           keccak256 (wordToBytes dst ++ wordToBytes 1))
    (hne_src : keccak256 (wordToBytes caller ++ wordToBytes 1) ≠ 0)
    (hne_dst : keccak256 (wordToBytes dst ++ wordToBytes 1) ≠ 0) :
    let src_slot := keccak256 (wordToBytes caller ++ wordToBytes 1)
    let dst_slot := keccak256 (wordToBytes dst ++ wordToBytes 1)
    ∃ s', execute code { State.init storage with calldata := calldata, caller := caller } 46
      = .done s'
    ∧ s'.storage src_slot = storage src_slot - amt
    ∧ s'.storage dst_slot = storage dst_slot + amt
    ∧ s'.storage 0 = storage 0 := by
  rw [transfer_asm] at hasm
  injection hasm with hcode
  subst hcode
  exact transfer_correct storage calldata _ _ _ hdst hamt hbal hne hne_src hne_dst

/-- Revert path: if balance is insufficient, execution reverts. -/
theorem transfer_revert (storage : Nat → Word) (calldata : List UInt8)
    (caller amt : Nat)
    (hamt : calldataWord calldata 0x24 = amt)
    (hbal : storage (keccak256 (wordToBytes caller ++ wordToBytes 1)) < amt) :
    execute tCode { State.init storage with calldata := calldata, caller := caller } 46
      = .reverted := by
  subst hamt
  rw [transfer_phase1, extractMem_src, transfer_phase2a]
  simp only [if_pos hbal]
  rw [transfer_phase2b_revert]

/-- Ledger bridge: connects EVM execution result back to `Scaled.transfer`.
    After executing transfer bytecode, storage reflects the ledger's transfer operation:
    - `balances[src] -= amt`
    - `balances[dst] += amt`
    - `totalSupply` unchanged -/
theorem transfer_matches_ledger {n : Nat} [NeZero n] (l : Scaled.Ledger n)
    (calldata : List UInt8) (src dst : Fin n) (amt : Nat)
    (hdst : calldataWord calldata 4 = dst.val)
    (hamt : calldataWord calldata 0x24 = amt)
    (storageSlot : Nat → Word)
    (hbal_src : storageSlot (keccak256 (wordToBytes src.val ++ wordToBytes 1)) = l.balances src)
    (hbal_dst : storageSlot (keccak256 (wordToBytes dst.val ++ wordToBytes 1)) = l.balances dst)
    (hsup : storageSlot 0 = l.totalSupply)
    (hbal : amt ≤ l.balances src)
    (hne : keccak256 (wordToBytes src.val ++ wordToBytes 1) ≠
           keccak256 (wordToBytes dst.val ++ wordToBytes 1))
    (hne_src : keccak256 (wordToBytes src.val ++ wordToBytes 1) ≠ 0)
    (hne_dst : keccak256 (wordToBytes dst.val ++ wordToBytes 1) ≠ 0) :
    ∃ s', execute tCode
      { State.init storageSlot with calldata := calldata, caller := src.val } 46
      = .done s'
    ∧ s'.storage (keccak256 (wordToBytes src.val ++ wordToBytes 1))
        = l.balances src - amt
    ∧ s'.storage (keccak256 (wordToBytes dst.val ++ wordToBytes 1))
        = l.balances dst + amt
    ∧ s'.storage 0 = l.totalSupply := by
  have hbal' : amt ≤ storageSlot (keccak256 (wordToBytes src.val ++ wordToBytes 1)) := by
    rw [hbal_src]; exact hbal
  have ⟨s', hexec, hsrc, hdst_bal, hsup'⟩ :=
    transfer_correct storageSlot calldata _ _ _ hdst hamt hbal' hne hne_src hne_dst
  exact ⟨s', hexec, by rw [hsrc, hbal_src], by rw [hdst_bal, hbal_dst], by rw [hsup', hsup]⟩

end EVM
