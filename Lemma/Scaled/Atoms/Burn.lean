import Lemma.Scaled.Ledger

open Scaled

variable {n : Nat} [NeZero n]

/-- Burn `amt` tokens from `src`.
    Requires `amt ≤ balances src`. -/
def Scaled.burn (l : Ledger n) (src : Fin n) (amt : Nat)
    (hAmt : amt ≤ l.balances src)
    : { l' : Ledger n //
        l'.totalSupply = l.totalSupply - amt
      ∧ l'.balances src = l.balances src - amt } :=
  let newBal := Function.update l.balances src (l.balances src - amt)
  ⟨ { balances := newBal
    , totalSupply := l.totalSupply - amt
    , inv := by
        simp only [newBal]
        rw [l.inv, sum_update_sub _ _ _ hAmt]
    }
  , by
      exact ⟨rfl, by simp [newBal, Function.update_self]⟩
  ⟩
