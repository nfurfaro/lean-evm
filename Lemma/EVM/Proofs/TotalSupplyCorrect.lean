import Lemma.EVM.Exec
import Lemma.EVM.Proofs.TotalSupplyAsm
import Lemma.Scaled.Ledger

/-!
# totalSupply Correctness Proof

Proves that executing the assembled `totalSupplyCode` bytecode returns
the value at storage slot 0, encoded as a 32-byte big-endian word.

## Execution trace (7 steps on 11 bytes)

| Step | PC | Instr     | Stack        | Memory  |
|------|----|-----------|--------------|---------|
| 0    | 0  | PUSH1 0   | [] → [0]     | default |
| 1    | 2  | SLOAD     | [0] → [v]   | default |
| 2    | 3  | PUSH1 0   | [v] → [0,v] | default |
| 3    | 5  | MSTORE    | [0,v] → []  | m[0]:=v |
| 4    | 6  | PUSH1 32  | [] → [32]   | m[0]=v  |
| 5    | 8  | PUSH1 0   | [32] → [0,32] | m[0]=v |
| 6    | 10 | RETURN    | [0,32] → halt | ret m[0:32] |
-/

namespace EVM

private def tsCode : List UInt8 :=
  [0x60, 0x00, 0x54, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]

/-- Helper: extracting 32 bytes from memory after writing a word at offset 0
    yields the same bytes as `wordToBytes`. -/
theorem extractMemBytes_writeMem_zero (v : Word) :
    extractMemBytes (writeMem Memory.default 0 v) 0 32 = wordToBytes v := by
  simp [extractMemBytes, writeMem, wordToBytes]
  intro a ha
  simp [ha, Word.toBytes32, Nat.mod_eq_of_lt ha]

/-- Core theorem: executing the totalSupply bytecode returns storage[0] as 32 big-endian bytes. -/
theorem totalSupply_correct (storage : Nat → Word) (v : Nat) (hstorage : storage 0 = v) :
    ∃ data s', execute tsCode (State.init storage) 8 = .returned data s'
    ∧ data = wordToBytes v := by
  subst hstorage
  exact ⟨_, _, rfl, extractMemBytes_writeMem_zero (storage 0)⟩

/-- Codegen corollary: connects to the `assemble` function. -/
theorem totalSupply_codegen_correct (storage : Nat → Word)
    (code : List UInt8) (hasm : assemble Codegen.totalSupplyCode = some code)
    (v : Nat) (hstorage : storage 0 = v) :
    ∃ data s', execute code (State.init storage) 8 = .returned data s'
    ∧ data = wordToBytes v := by
  rw [totalSupply_asm] at hasm
  injection hasm with hcode
  subst hcode
  exact totalSupply_correct storage v hstorage

/-- Ledger bridge: connects EVM execution result back to `Scaled.Ledger.totalSupply`. -/
theorem totalSupply_matches_ledger {n : Nat} [NeZero n] (l : Scaled.Ledger n) :
    ∃ data s', execute tsCode
      (State.init (fun slot => if slot == 0 then l.totalSupply else 0)) 8
      = .returned data s'
    ∧ data = wordToBytes l.totalSupply := by
  apply totalSupply_correct
  simp

end EVM
