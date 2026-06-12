import Lemma.EVM.Exec
import Lemma.EVM.Proofs.RuntimeAsm
import Lemma.EVM.Proofs.TotalSupplyCorrect
import Lemma.EVM.Proofs.BalanceOfCorrect
import Lemma.EVM.Proofs.MintCorrect
import Lemma.EVM.Proofs.TransferCorrect

/-!
# Dispatch Correctness Proofs

Proves end-to-end correctness: executing the assembled `runtimeCode` with a
given selector produces the same result as the isolated function proof.

Four theorems:
1. `runtime_totalSupply_correct` — selector 0x18160ddd → returns storage[0]
2. `runtime_balanceOf_correct` — selector 0x70a08231 → returns storage[hash(addr,1)]
3. `runtime_mint_correct` — selector 0x40c10f19 → updates storage correctly
4. `runtime_transfer_correct` — selector 0xa9059cbb → updates two balance slots

Labels: mint=50, transfer=86, totalSupply=147, balanceOf=159
-/

namespace EVM

/-- The 185-byte assembled runtime bytecode. -/
private def rtCode : List UInt8 :=
  [0x60, 0x00, 0x35, 0x60, 0xe0, 0x1c, 0x80, 0x63, 0x40, 0xc1,
   0x0f, 0x19, 0x14, 0x60, 0x32, 0x57, 0x80, 0x63, 0x18, 0x16,
   0x0d, 0xdd, 0x14, 0x60, 0x93, 0x57, 0x80, 0x63, 0xa9, 0x05,
   0x9c, 0xbb, 0x14, 0x60, 0x56, 0x57, 0x63, 0x70, 0xa0, 0x82,
   0x31, 0x14, 0x60, 0x9f, 0x57, 0x60, 0x00, 0x60, 0x00, 0xfd,
   0x5b, 0x60, 0x04, 0x35, 0x60, 0x24, 0x35, 0x81, 0x60, 0x00,
   0x52, 0x60, 0x01, 0x60, 0x20, 0x52, 0x60, 0x40, 0x60, 0x00,
   0x20, 0x80, 0x54, 0x82, 0x01, 0x90, 0x55, 0x60, 0x00, 0x54,
   0x01, 0x60, 0x00, 0x55, 0x50, 0x00, 0x5b, 0x33, 0x60, 0x04,
   0x35, 0x60, 0x24, 0x35, 0x82, 0x60, 0x00, 0x52, 0x60, 0x01,
   0x60, 0x20, 0x52, 0x60, 0x40, 0x60, 0x00, 0x20, 0x80, 0x54,
   0x82, 0x81, 0x10, 0x15, 0x60, 0x7a, 0x57, 0x60, 0x00, 0x60,
   0x00, 0xfd, 0x5b, 0x82, 0x90, 0x03, 0x90, 0x55, 0x81, 0x60,
   0x00, 0x52, 0x60, 0x40, 0x60, 0x00, 0x20, 0x80, 0x54, 0x82,
   0x01, 0x90, 0x55, 0x50, 0x50, 0x50, 0x00, 0x5b, 0x60, 0x00,
   0x54, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3, 0x5b,
   0x60, 0x04, 0x35, 0x60, 0x00, 0x52, 0x60, 0x01, 0x60, 0x20,
   0x52, 0x60, 0x40, 0x60, 0x00, 0x20, 0x54, 0x60, 0x00, 0x52,
   0x60, 0x20, 0x60, 0x00, 0xf3]

-- ═══════════════════════════════════════════════════════════════
-- Shared: selector extraction (4 steps, PC 0→6)
-- ═══════════════════════════════════════════════════════════════

private theorem selector_extract (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word) (fuel : Nat) :
    execute rtCode { State.init storage with calldata := calldata, caller := caller } (fuel + 4) =
    execute rtCode
      { pc := 6, stack := [calldataWord calldata 0 >>> 224],
        memory := Memory.default, storage := storage, calldata := calldata,
        caller := caller } fuel := by
  rfl

-- ═══════════════════════════════════════════════════════════════
-- 1. totalSupply: selector 0x18160ddd → returns storage[0]
-- ═══════════════════════════════════════════════════════════════

set_option maxHeartbeats 1600000 in
/-- Dispatch to totalSupply label (11 steps, PC 6→148). -/
private theorem ts_dispatch (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word) :
    execute rtCode
      { pc := 6, stack := [0x18160ddd],
        memory := Memory.default, storage := storage, calldata := calldata,
        caller := caller } 18 =
    execute rtCode
      { pc := 148, stack := [0x18160ddd],
        memory := Memory.default, storage := storage, calldata := calldata,
        caller := caller } 7 := by
  rfl

/-- totalSupply body (7 steps, PC 148→RETURN). -/
private theorem ts_body (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word) :
    execute rtCode
      { pc := 148, stack := [0x18160ddd],
        memory := Memory.default, storage := storage, calldata := calldata,
        caller := caller } 7 =
    .returned (extractMemBytes (writeMem Memory.default 0 (storage 0)) 0 32)
      { pc := 158, stack := [0, 32, 0x18160ddd],
        memory := writeMem Memory.default 0 (storage 0),
        storage := storage, calldata := calldata,
        caller := caller } := by
  rfl

/-- Executing runtimeCode with selector 0x18160ddd returns storage[0]. -/
theorem runtime_totalSupply_correct (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word)
    (hsel : calldataWord calldata 0 >>> 224 = 0x18160ddd) :
    ∃ data s', execute rtCode
        { State.init storage with calldata := calldata, caller := caller } 22
      = .returned data s'
    ∧ data = wordToBytes (storage 0) := by
  rw [show 22 = 18 + 4 from rfl, selector_extract, hsel, ts_dispatch, ts_body]
  exact ⟨_, _, rfl, extractMemBytes_writeMem_zero (storage 0)⟩

-- ═══════════════════════════════════════════════════════════════
-- 2. balanceOf: selector 0x70a08231 → returns storage[hash(addr,1)]
-- ═══════════════════════════════════════════════════════════════

set_option maxHeartbeats 4000000 in
/-- Dispatch to balanceOf label (20 steps, PC 6→160). -/
private theorem bof_dispatch (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word) :
    execute rtCode
      { pc := 6, stack := [0x70a08231],
        memory := Memory.default, storage := storage, calldata := calldata,
        caller := caller } 36 =
    execute rtCode
      { pc := 160, stack := [],
        memory := Memory.default, storage := storage, calldata := calldata,
        caller := caller } 16 := by
  rfl

set_option maxHeartbeats 1600000 in
/-- balanceOf body prefix: 10 steps through SHA3 (PC 160→176). -/
private theorem bof_body_prefix (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word) :
    execute rtCode
      { pc := 160, stack := [],
        memory := Memory.default, storage := storage, calldata := calldata,
        caller := caller } 16 =
    execute rtCode
      { pc := 176,
        stack := [keccak256 (extractMemBytes
          (writeMem (writeMem Memory.default 0 (calldataWord calldata 4)) 32 1) 0 64)],
        memory := writeMem (writeMem Memory.default 0 (calldataWord calldata 4)) 32 1,
        storage := storage, calldata := calldata,
        caller := caller } 6 := by
  rfl

/-- balanceOf body suffix: 6 steps SLOAD through RETURN (PC 176→184). -/
private theorem bof_body_suffix (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word) (slot : Nat) (mem : Nat → Bytes32) :
    execute rtCode
      { pc := 176, stack := [slot], memory := mem,
        storage := storage, calldata := calldata,
        caller := caller } 6 =
    .returned (extractMemBytes (writeMem mem 0 (storage slot)) 0 32)
      { pc := 184, stack := [0, 32],
        memory := writeMem mem 0 (storage slot),
        storage := storage, calldata := calldata,
        caller := caller } := by
  rfl

/-- Executing runtimeCode with selector 0x70a08231 returns storage[hash(addr,1)]. -/
theorem runtime_balanceOf_correct (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word)
    (hsel : calldataWord calldata 0 >>> 224 = 0x70a08231)
    (addr bal : Nat)
    (haddr : calldataWord calldata 4 = addr)
    (hbal : storage (keccak256 (wordToBytes addr ++ wordToBytes 1)) = bal) :
    ∃ data s', execute rtCode
        { State.init storage with calldata := calldata, caller := caller } 40
      = .returned data s'
    ∧ data = wordToBytes bal := by
  subst haddr; subst hbal
  rw [show 40 = 36 + 4 from rfl, selector_extract, hsel, bof_dispatch,
      bof_body_prefix, bof_body_suffix]
  exact ⟨_, _, rfl, by rw [extractMemBytes_writeMem_zero_gen, extractMemBytes_two_words]⟩

-- ═══════════════════════════════════════════════════════════════
-- 3. mint: selector 0x40c10f19 → updates storage correctly
-- ═══════════════════════════════════════════════════════════════

/-- Dispatch to mint label (6 steps, PC 6→51). -/
private theorem mint_dispatch (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word) :
    execute rtCode
      { pc := 6, stack := [0x40c10f19],
        memory := Memory.default, storage := storage, calldata := calldata,
        caller := caller } 32 =
    execute rtCode
      { pc := 51, stack := [0x40c10f19],
        memory := Memory.default, storage := storage, calldata := calldata,
        caller := caller } 26 := by
  rfl

set_option maxHeartbeats 1600000 in
/-- Mint body phase 1: 13 steps through SHA3 (PC 51→71). -/
private theorem mint_body_phase1 (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word) :
    execute rtCode
      { pc := 51, stack := [0x40c10f19],
        memory := Memory.default, storage := storage, calldata := calldata,
        caller := caller } 26 =
    execute rtCode
      { pc := 71,
        stack := [keccak256 (extractMemBytes
          (writeMem (writeMem Memory.default 0 (calldataWord calldata 4)) 32 1) 0 64),
          calldataWord calldata 0x24, calldataWord calldata 4, 0x40c10f19],
        memory := writeMem (writeMem Memory.default 0 (calldataWord calldata 4)) 32 1,
        storage := storage, calldata := calldata,
        caller := caller } 13 := by
  rfl

/-- Mint body phase 2: balance SLOAD + ADD + SSTORE (6 steps, PC 71→77). -/
private theorem mint_body_phase2 (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word) (bal_slot amt dst sel : Nat) (mem : Nat → Bytes32) :
    execute rtCode
      { pc := 71, stack := [bal_slot, amt, dst, sel],
        memory := mem, storage := storage, calldata := calldata,
        caller := caller } 13 =
    execute rtCode
      { pc := 77, stack := [amt, dst, sel],
        memory := mem,
        storage := fun k => if k = bal_slot then amt + storage bal_slot else storage k,
        calldata := calldata,
        caller := caller } 7 := by
  rfl

/-- Mint body phase 3: totalSupply update + POP + STOP (7 steps, PC 77→halt). -/
private theorem mint_body_phase3 (sto : Nat → Word) (calldata : List UInt8)
    (caller : Word) (amt dst sel : Nat) (mem : Nat → Bytes32) :
    execute rtCode
      { pc := 77, stack := [amt, dst, sel],
        memory := mem, storage := sto, calldata := calldata,
        caller := caller } 7 =
    .done
      { pc := 85, stack := [sel],
        memory := mem,
        storage := fun k => if k = 0 then sto 0 + amt else sto k,
        calldata := calldata,
        caller := caller } := by
  rfl

/-- Executing runtimeCode with selector 0x40c10f19 updates storage correctly. -/
theorem runtime_mint_correct (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word)
    (hsel : calldataWord calldata 0 >>> 224 = 0x40c10f19)
    (dst amt : Nat)
    (hdst : calldataWord calldata 4 = dst)
    (hamt : calldataWord calldata 0x24 = amt)
    (hne : keccak256 (wordToBytes dst ++ wordToBytes 1) ≠ 0) :
    ∃ s', execute rtCode
        { State.init storage with calldata := calldata, caller := caller } 36
      = .done s'
    ∧ s'.storage (keccak256 (wordToBytes dst ++ wordToBytes 1))
        = storage (keccak256 (wordToBytes dst ++ wordToBytes 1)) + amt
    ∧ s'.storage 0 = storage 0 + amt := by
  subst hdst; subst hamt
  rw [show 36 = 32 + 4 from rfl, selector_extract, hsel,
      mint_dispatch, mint_body_phase1, extractMemBytes_two_words',
      mint_body_phase2, mint_body_phase3]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp [hne, Nat.add_comm]
  · simp [Ne.symm hne]

-- ═══════════════════════════════════════════════════════════════
-- 4. transfer: selector 0xa9059cbb → updates two balance slots
-- ═══════════════════════════════════════════════════════════════

set_option maxHeartbeats 2000000 in
/-- Dispatch to transfer label (16 steps, PC 6→87). -/
private theorem xfer_dispatch (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word) :
    execute rtCode
      { pc := 6, stack := [0xa9059cbb],
        memory := Memory.default, storage := storage, calldata := calldata,
        caller := caller } 62 =
    execute rtCode
      { pc := 87, stack := [0xa9059cbb],
        memory := Memory.default, storage := storage, calldata := calldata,
        caller := caller } 46 := by
  rfl

set_option maxHeartbeats 1600000 in
/-- Transfer body phase 1: CALLER + load args + compute src_slot (14 steps, PC 87→108). -/
private theorem xfer_phase1 (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word) :
    execute rtCode
      { pc := 87, stack := [0xa9059cbb],
        memory := Memory.default, storage := storage, calldata := calldata,
        caller := caller } 46 =
    execute rtCode
      { pc := 108,
        stack := [keccak256 (extractMemBytes
          (writeMem (writeMem Memory.default 0 caller) 32 1) 0 64),
          calldataWord calldata 0x24, calldataWord calldata 4, caller, 0xa9059cbb],
        memory := writeMem (writeMem Memory.default 0 caller) 32 1,
        storage := storage, calldata := calldata,
        caller := caller } 32 := by
  rfl

/-- Transfer phase 2a: DUP1 + SLOAD + DUP3 + DUP2 + LT (5 steps, PC 108→113).
    Produces `if storage src_slot < amt then 1 else 0` on stack. -/
private theorem xfer_phase2a
    (storage : Nat → Word) (calldata : List UInt8) (caller : Word)
    (src_slot amt dst src sel : Nat) (mem : Nat → Bytes32) :
    execute rtCode
      { pc := 108, stack := [src_slot, amt, dst, src, sel],
        memory := mem, storage := storage, calldata := calldata,
        caller := caller } 32 =
    execute rtCode
      { pc := 113,
        stack := [if storage src_slot < amt then 1 else 0,
                  storage src_slot, src_slot, amt, dst, src, sel],
        memory := mem, storage := storage, calldata := calldata,
        caller := caller } 27 := by
  rfl

/-- Transfer phase 2b (success): ISZERO + PUSH + JUMPI + JUMPDEST (4 steps, PC 113→123).
    After resolving LT result to 0 (balance sufficient). -/
private theorem xfer_phase2b_success
    (storage : Nat → Word) (calldata : List UInt8) (caller : Word)
    (src_bal src_slot amt dst src sel : Nat) (mem : Nat → Bytes32) :
    execute rtCode
      { pc := 113, stack := [0, src_bal, src_slot, amt, dst, src, sel],
        memory := mem, storage := storage, calldata := calldata,
        caller := caller } 27 =
    execute rtCode
      { pc := 123, stack := [src_bal, src_slot, amt, dst, src, sel],
        memory := mem, storage := storage, calldata := calldata,
        caller := caller } 23 := by
  rfl

/-- Transfer phase 2b (revert): ISZERO + PUSH + JUMPI + PUSH + PUSH + REVERT
    (6 steps from PC 113). After resolving LT result to 1 (balance insufficient). -/
private theorem xfer_phase2b_revert
    (storage : Nat → Word) (calldata : List UInt8) (caller : Word)
    (src_bal src_slot amt dst src sel : Nat) (mem : Nat → Bytes32) :
    execute rtCode
      { pc := 113, stack := [1, src_bal, src_slot, amt, dst, src, sel],
        memory := mem, storage := storage, calldata := calldata,
        caller := caller } 27 =
    .reverted := by
  rfl

/-- Transfer phase 3: DUP3 + SWAP1 + SUB + SWAP1 + SSTORE (5 steps, PC 123→128).
    Updates src balance: storage[src_slot] = src_bal - amt. -/
private theorem xfer_phase3
    (storage : Nat → Word) (calldata : List UInt8) (caller : Word)
    (src_bal src_slot amt dst src sel : Nat) (mem : Nat → Bytes32) :
    execute rtCode
      { pc := 123, stack := [src_bal, src_slot, amt, dst, src, sel],
        memory := mem, storage := storage, calldata := calldata,
        caller := caller } 23 =
    execute rtCode
      { pc := 128, stack := [amt, dst, src, sel],
        memory := mem,
        storage := fun k => if k = src_slot then src_bal - amt else storage k,
        calldata := calldata,
        caller := caller } 18 := by
  rfl

set_option maxHeartbeats 1600000 in
/-- Transfer phase 4: DUP2 + PUSH + MSTORE + PUSH + PUSH + SHA3 (6 steps, PC 128→137).
    Computes dst_slot = keccak256(dst, 1). -/
private theorem xfer_phase4
    (sto : Nat → Word) (calldata : List UInt8) (caller : Word)
    (amt dst src sel : Nat) (mem : Nat → Bytes32) :
    execute rtCode
      { pc := 128, stack := [amt, dst, src, sel],
        memory := mem, storage := sto, calldata := calldata,
        caller := caller } 18 =
    execute rtCode
      { pc := 137,
        stack := [keccak256 (extractMemBytes (writeMem mem 0 dst) 0 64),
                  amt, dst, src, sel],
        memory := writeMem mem 0 dst,
        storage := sto, calldata := calldata,
        caller := caller } 12 := by
  rfl

/-- Transfer phase 5: DUP1 + SLOAD + DUP3 + ADD + SWAP1 + SSTORE + POP×3 + STOP
    (10 steps, PC 137→halt). Updates dst balance and halts. -/
private theorem xfer_phase5
    (sto : Nat → Word) (calldata : List UInt8) (caller : Word)
    (dst_slot amt dst src sel : Nat) (mem : Nat → Bytes32) :
    execute rtCode
      { pc := 137, stack := [dst_slot, amt, dst, src, sel],
        memory := mem, storage := sto, calldata := calldata,
        caller := caller } 12 =
    .done
      { pc := 146, stack := [sel],
        memory := mem,
        storage := fun k => if k = dst_slot then amt + sto dst_slot else sto k,
        calldata := calldata,
        caller := caller } := by
  rfl

/-- Executing runtimeCode with selector 0xa9059cbb updates storage correctly (success path).
    - `storage[src_slot] -= amt`
    - `storage[dst_slot] += amt`
    - `storage[0]` (totalSupply) is unchanged
    where src_slot = keccak256(wordToBytes caller ++ wordToBytes 1)
      and dst_slot = keccak256(wordToBytes dst ++ wordToBytes 1). -/
theorem runtime_transfer_correct (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word)
    (hsel : calldataWord calldata 0 >>> 224 = 0xa9059cbb)
    (dst amt : Nat)
    (hdst : calldataWord calldata 4 = dst)
    (hamt : calldataWord calldata 0x24 = amt)
    (hbal : amt ≤ storage (keccak256 (wordToBytes caller ++ wordToBytes 1)))
    (hne : keccak256 (wordToBytes caller ++ wordToBytes 1) ≠
           keccak256 (wordToBytes dst ++ wordToBytes 1))
    (hne_src : keccak256 (wordToBytes caller ++ wordToBytes 1) ≠ 0)
    (hne_dst : keccak256 (wordToBytes dst ++ wordToBytes 1) ≠ 0) :
    let src_slot := keccak256 (wordToBytes caller ++ wordToBytes 1)
    let dst_slot := keccak256 (wordToBytes dst ++ wordToBytes 1)
    ∃ s', execute rtCode
        { State.init storage with calldata := calldata, caller := caller } 66
      = .done s'
    ∧ s'.storage src_slot = storage src_slot - amt
    ∧ s'.storage dst_slot = storage dst_slot + amt
    ∧ s'.storage 0 = storage 0 := by
  subst hdst; subst hamt
  rw [show 66 = 62 + 4 from rfl, selector_extract, hsel,
      xfer_dispatch, xfer_phase1, extractMem_src,
      xfer_phase2a]
  have hlt : ¬ storage (keccak256 (wordToBytes caller ++ wordToBytes 1)) <
             calldataWord calldata 36 := not_lt.mpr hbal
  simp only [if_neg hlt]
  rw [xfer_phase2b_success, xfer_phase3, xfer_phase4,
      extractMem_dst, xfer_phase5]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp [hne]
  · simp [Ne.symm hne, Nat.add_comm]
  · simp [Ne.symm hne_dst, Ne.symm hne_src]

/-- Revert path: if balance is insufficient, execution reverts. -/
theorem runtime_transfer_revert (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word)
    (hsel : calldataWord calldata 0 >>> 224 = 0xa9059cbb)
    (amt : Nat)
    (hamt : calldataWord calldata 0x24 = amt)
    (hbal : storage (keccak256 (wordToBytes caller ++ wordToBytes 1)) < amt) :
    execute rtCode
        { State.init storage with calldata := calldata, caller := caller } 66
      = .reverted := by
  subst hamt
  rw [show 66 = 62 + 4 from rfl, selector_extract, hsel,
      xfer_dispatch, xfer_phase1, extractMem_src, xfer_phase2a]
  simp only [if_pos hbal]
  rw [xfer_phase2b_revert]

-- ═══════════════════════════════════════════════════════════════
-- Codegen corollaries: connect to assemble Codegen.runtimeCode
-- ═══════════════════════════════════════════════════════════════

theorem runtime_totalSupply_codegen (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word)
    (code : List UInt8) (hasm : assemble Codegen.runtimeCode = some code)
    (hsel : calldataWord calldata 0 >>> 224 = 0x18160ddd) :
    ∃ data s', execute code
        { State.init storage with calldata := calldata, caller := caller } 22
      = .returned data s'
    ∧ data = wordToBytes (storage 0) := by
  rw [runtime_asm] at hasm; injection hasm with hcode; subst hcode
  exact runtime_totalSupply_correct storage calldata caller hsel

theorem runtime_balanceOf_codegen (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word)
    (code : List UInt8) (hasm : assemble Codegen.runtimeCode = some code)
    (hsel : calldataWord calldata 0 >>> 224 = 0x70a08231)
    (addr bal : Nat)
    (haddr : calldataWord calldata 4 = addr)
    (hbal : storage (keccak256 (wordToBytes addr ++ wordToBytes 1)) = bal) :
    ∃ data s', execute code
        { State.init storage with calldata := calldata, caller := caller } 40
      = .returned data s'
    ∧ data = wordToBytes bal := by
  rw [runtime_asm] at hasm; injection hasm with hcode; subst hcode
  exact runtime_balanceOf_correct storage calldata caller hsel addr bal haddr hbal

theorem runtime_mint_codegen (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word)
    (code : List UInt8) (hasm : assemble Codegen.runtimeCode = some code)
    (hsel : calldataWord calldata 0 >>> 224 = 0x40c10f19)
    (dst amt : Nat)
    (hdst : calldataWord calldata 4 = dst)
    (hamt : calldataWord calldata 0x24 = amt)
    (hne : keccak256 (wordToBytes dst ++ wordToBytes 1) ≠ 0) :
    ∃ s', execute code
        { State.init storage with calldata := calldata, caller := caller } 36
      = .done s'
    ∧ s'.storage (keccak256 (wordToBytes dst ++ wordToBytes 1))
        = storage (keccak256 (wordToBytes dst ++ wordToBytes 1)) + amt
    ∧ s'.storage 0 = storage 0 + amt := by
  rw [runtime_asm] at hasm; injection hasm with hcode; subst hcode
  exact runtime_mint_correct storage calldata caller hsel dst amt hdst hamt hne

theorem runtime_transfer_codegen (storage : Nat → Word) (calldata : List UInt8)
    (caller : Word)
    (code : List UInt8) (hasm : assemble Codegen.runtimeCode = some code)
    (hsel : calldataWord calldata 0 >>> 224 = 0xa9059cbb)
    (dst amt : Nat)
    (hdst : calldataWord calldata 4 = dst)
    (hamt : calldataWord calldata 0x24 = amt)
    (hbal : amt ≤ storage (keccak256 (wordToBytes caller ++ wordToBytes 1)))
    (hne : keccak256 (wordToBytes caller ++ wordToBytes 1) ≠
           keccak256 (wordToBytes dst ++ wordToBytes 1))
    (hne_src : keccak256 (wordToBytes caller ++ wordToBytes 1) ≠ 0)
    (hne_dst : keccak256 (wordToBytes dst ++ wordToBytes 1) ≠ 0) :
    let src_slot := keccak256 (wordToBytes caller ++ wordToBytes 1)
    let dst_slot := keccak256 (wordToBytes dst ++ wordToBytes 1)
    ∃ s', execute code
        { State.init storage with calldata := calldata, caller := caller } 66
      = .done s'
    ∧ s'.storage src_slot = storage src_slot - amt
    ∧ s'.storage dst_slot = storage dst_slot + amt
    ∧ s'.storage 0 = storage 0 := by
  rw [runtime_asm] at hasm; injection hasm with hcode; subst hcode
  exact runtime_transfer_correct storage calldata caller hsel dst amt hdst hamt hbal hne
    hne_src hne_dst

end EVM
