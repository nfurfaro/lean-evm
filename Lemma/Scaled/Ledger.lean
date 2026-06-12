import Lemma.Scaled.Basic

/-!
# Scaled Ledger

Ledger parameterized by `Fin n` with supply conservation via `Finset.univ.sum`.
-/

namespace Scaled

/-- A ledger with supply conservation enforced by the type system.
    Parameterized by address space size `n`. -/
structure Ledger (n : Nat) [NeZero n] where
  balances : Fin n → Nat
  totalSupply : Nat
  inv : totalSupply = Finset.univ.sum balances

variable {n : Nat} [NeZero n]

/-- The empty ledger: all balances zero, total supply zero. -/
def Ledger.empty : Scaled.Ledger n where
  balances := fun _ => 0
  totalSupply := 0
  inv := by simp

end Scaled
