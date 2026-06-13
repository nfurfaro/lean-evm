import Lemma.Scaled.Ledger

open Scaled

variable {n : Nat} [NeZero n]

/-- Mint `amt` new tokens to `dst`.
    Return type guarantees supply increases by `amt` and dst balance increases by `amt`. -/
def Scaled.mint (l : Ledger n) (dst : Fin n) (amt : Nat)
    : { l' : Ledger n //
        l'.totalSupply = l.totalSupply + amt
      ∧ l'.balances dst = l.balances dst + amt } :=
  let newBal := Function.update l.balances dst (l.balances dst + amt)
  ⟨ { balances := newBal
    , totalSupply := l.totalSupply + amt
    , inv := by
        simp only [newBal]
        rw [l.inv, sum_update_add]
    }
  , by
      exact ⟨rfl, by simp [newBal, Function.update_self]⟩
  ⟩
