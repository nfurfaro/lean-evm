import Lemma.EVM.Exec
import Lemma.EVM.Proofs.BalanceOfAsm
import Lemma.Scaled.Ledger

/-!
# balanceOf Correctness Proof

Proves that executing the assembled `balanceOfCode` bytecode returns
`storage[keccak256(addr ++ slot)]` as 32 bytes, where `addr` is read
from calldata and `slot = 1` is the balances mapping slot.

## Execution trace (16 steps on 25 bytes)

| Step | PC | Instr          | Stack             | Memory               |
|------|----|----------------|-------------------|----------------------|
| 0    | 0  | PUSH1 0x04     | [] → [4]          | default              |
| 1    | 2  | CALLDATALOAD   | [4] → [addr]      | default              |
| 2    | 3  | PUSH1 0x00     | [addr] → [0,addr] | default              |
| 3    | 5  | MSTORE         | [0,addr] → []     | m[0]:=addr           |
| 4    | 6  | PUSH1 0x01     | [] → [1]          | m[0]=addr            |
| 5    | 8  | PUSH1 0x20     | [1] → [32,1]      | m[0]=addr            |
| 6    | 10 | MSTORE         | [32,1] → []       | m[0]=addr, m[1]=1    |
| 7    | 11 | PUSH1 0x40     | [] → [64]         | m[0]=addr, m[1]=1    |
| 8    | 13 | PUSH1 0x00     | [64] → [0,64]     | m[0]=addr, m[1]=1    |
| 9    | 15 | SHA3           | [0,64] → [slot]   | m[0]=addr, m[1]=1    |
| 10   | 16 | SLOAD          | [slot] → [bal]    | m[0]=addr, m[1]=1    |
| 11   | 17 | PUSH1 0x00     | [bal] → [0,bal]   | m[0]=addr, m[1]=1    |
| 12   | 19 | MSTORE         | [0,bal] → []      | m[0]=bal             |
| 13   | 20 | PUSH1 0x20     | [] → [32]         | m[0]=bal             |
| 14   | 22 | PUSH1 0x00     | [32] → [0,32]     | m[0]=bal             |
| 15   | 24 | RETURN         | [0,32] → halt     | returns m[0:32]      |
-/

namespace EVM

private def bofCode : List UInt8 :=
  [0x60, 0x04, 0x35, 0x60, 0x00, 0x52, 0x60, 0x01, 0x60, 0x20, 0x52,
   0x60, 0x40, 0x60, 0x00, 0x20, 0x54, 0x60, 0x00, 0x52, 0x60, 0x20,
   0x60, 0x00, 0xf3]

-- ───────────────────────── Memory helpers ─────────────────────────

/-- Extracting 32 bytes after writing a word at offset 0 yields `wordToBytes`,
    for any base memory. -/
theorem extractMemBytes_writeMem_zero_gen (mem : Nat → Bytes32) (v : Word) :
    extractMemBytes (writeMem mem 0 v) 0 32 = wordToBytes v := by
  simp [extractMemBytes, writeMem, wordToBytes]
  intro a ha
  simp [ha, Word.toBytes32, Nat.mod_eq_of_lt ha]

/-- Splitting: extractMemBytes over (a+b) bytes = first a ++ next b. -/
private theorem extractMemBytes_append (mem : Nat → Bytes32) (off a b : Nat) :
    extractMemBytes mem off (a + b) =
    extractMemBytes mem off a ++ extractMemBytes mem (off + a) b := by
  simp only [extractMemBytes, List.range_add, List.map_append, List.map_map]
  congr 1
  simp only [Function.comp_def, Nat.add_assoc]

/-- First 32 bytes of two-word memory: yields `wordToBytes addr`. -/
private theorem extractMemBytes_word0 (addr : Word) :
    extractMemBytes (writeMem (writeMem Memory.default 0 addr) 32 1) 0 32
    = wordToBytes addr := by
  simp [extractMemBytes, writeMem, wordToBytes]
  intro a ha
  have h0 : a / 32 = 0 := by omega
  simp [h0, Nat.mod_eq_of_lt ha]
  split
  · simp [Word.toBytes32]
  · omega

/-- Second 32 bytes of two-word memory: yields `wordToBytes 1`. -/
private theorem extractMemBytes_word1 (addr : Word) :
    extractMemBytes (writeMem (writeMem Memory.default 0 addr) 32 1) 32 32
    = wordToBytes 1 := by
  simp [extractMemBytes, writeMem, wordToBytes]
  intro a ha
  have h1 : (32 + a) / 32 = 1 := by omega
  have h2 : (32 + a) % 32 = a := by omega
  simp [Nat.mod_eq_of_lt ha]
  split
  · simp [Word.toBytes32]
  · omega

/-- Two-word memory extraction: 64 bytes = concatenation of both words. -/
theorem extractMemBytes_two_words (addr : Word) :
    extractMemBytes (writeMem (writeMem Memory.default 0 addr) 32 1) 0 64
    = wordToBytes addr ++ wordToBytes 1 := by
  have h64 : (64 : Nat) = 32 + 32 := by omega
  rw [h64, extractMemBytes_append, extractMemBytes_word0, extractMemBytes_word1]

-- ───────────────────── Execution phasing ──────────────────────

set_option maxHeartbeats 400000 in
/-- Steps 0–9 (through SHA3). Split to keep each `rfl` within heartbeat budget. -/
private theorem balanceOf_exec_prefix (storage : Nat → Word) (calldata : List UInt8) :
    execute bofCode { State.init storage with calldata := calldata } 17 =
    execute bofCode
      { pc := 16
        stack := [keccak256 (extractMemBytes
          (writeMem (writeMem Memory.default 0 (calldataWord calldata 4)) 32 1) 0 64)]
        memory := writeMem (writeMem Memory.default 0 (calldataWord calldata 4)) 32 1
        storage := storage
        calldata := calldata } 7 := by
  rfl

/-- Steps 10–15 (SLOAD through RETURN). -/
private theorem balanceOf_exec_suffix (storage : Nat → Word) (calldata : List UInt8)
    (slot : Nat) (mem : Nat → Bytes32) :
    execute bofCode
      { pc := 16, stack := [slot], memory := mem,
        storage := storage, calldata := calldata } 7 =
    .returned (extractMemBytes (writeMem mem 0 (storage slot)) 0 32)
      { pc := 24, stack := [0, 32], memory := writeMem mem 0 (storage slot),
        storage := storage, calldata := calldata } := by
  rfl

-- ───────────────────── Main theorems ──────────────────────

/-- Core theorem: executing the balanceOf bytecode returns
    `storage[keccak256(wordToBytes addr ++ wordToBytes 1)]` as 32 big-endian bytes. -/
theorem balanceOf_correct (storage : Nat → Word) (calldata : List UInt8)
    (addr bal : Nat)
    (haddr : calldataWord calldata 4 = addr)
    (hbal : storage (keccak256 (wordToBytes addr ++ wordToBytes 1)) = bal) :
    ∃ data s', execute bofCode
      { State.init storage with calldata := calldata } 17 = .returned data s'
    ∧ data = wordToBytes bal := by
  subst haddr; subst hbal
  rw [balanceOf_exec_prefix, balanceOf_exec_suffix]
  exact ⟨_, _, rfl, by rw [extractMemBytes_writeMem_zero_gen, extractMemBytes_two_words]⟩

/-- Codegen corollary: connects to the `assemble` function. -/
theorem balanceOf_codegen_correct (storage : Nat → Word) (calldata : List UInt8)
    (code : List UInt8) (hasm : assemble Codegen.balanceOfCode = some code)
    (addr bal : Nat)
    (haddr : calldataWord calldata 4 = addr)
    (hbal : storage (keccak256 (wordToBytes addr ++ wordToBytes 1)) = bal) :
    ∃ data s', execute code { State.init storage with calldata := calldata } 17
      = .returned data s'
    ∧ data = wordToBytes bal := by
  rw [balanceOf_asm] at hasm
  injection hasm with hcode
  subst hcode
  exact balanceOf_correct storage calldata addr _ haddr hbal

/-- Ledger bridge: connects EVM execution result back to `Scaled.Ledger.balances`. -/
theorem balanceOf_matches_ledger {n : Nat} [NeZero n] (l : Scaled.Ledger n)
    (calldata : List UInt8) (who : Fin n)
    (haddr : calldataWord calldata 4 = who.val)
    (storageSlot : Nat → Word)
    (hslot : storageSlot (keccak256 (wordToBytes who.val ++ wordToBytes 1)) = l.balances who) :
    ∃ data s', execute bofCode
      { State.init storageSlot with calldata := calldata } 17
      = .returned data s'
    ∧ data = wordToBytes (l.balances who) := by
  exact balanceOf_correct storageSlot calldata who.val _ haddr hslot

end EVM
