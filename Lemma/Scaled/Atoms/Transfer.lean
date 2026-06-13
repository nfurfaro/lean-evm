import Lemma.Scaled.Ledger

open Scaled

variable {n : Nat} [NeZero n]

/-- Transfer `amt` from `src` to `dst`.
    Requires sufficient balance and distinct addresses.

    The proof composes `sum_update_sub` and `sum_update_add`:
    after subtracting `amt` from `src` and adding `amt` to `dst`,
    the net effect on the total sum is zero. -/
def Scaled.transfer (l : Ledger n) (src dst : Fin n) (amt : Nat)
    (hAmt : amt ≤ l.balances src)
    (hNeq : src ≠ dst)
    : { l' : Ledger n //
        l'.totalSupply = l.totalSupply
      ∧ l'.balances src = l.balances src - amt
      ∧ l'.balances dst = l.balances dst + amt } :=
  let step1 := Function.update l.balances src (l.balances src - amt)
  let newBal := Function.update step1 dst (l.balances dst + amt)
  have hStep1Dst : step1 dst = l.balances dst :=
    Function.update_of_ne (Ne.symm hNeq) _ _
  ⟨ { balances := newBal
    , totalSupply := l.totalSupply
    , inv := by
        -- We need: l.totalSupply = Finset.univ.sum newBal
        -- Chain: newBal sum = step1 sum + amt = (original sum - amt) + amt = original sum
        simp only [newBal]
        rw [← hStep1Dst, sum_update_add]
        -- Goal: l.totalSupply = Finset.univ.sum step1 + amt
        have hSub : Finset.univ.sum step1 = Finset.univ.sum l.balances - amt := by
          simp only [step1]
          exact sum_update_sub l.balances src amt hAmt
        rw [hSub, l.inv]
        -- Goal: Finset.univ.sum l.balances = Finset.univ.sum l.balances - amt + amt
        have hAmtLeSum : amt ≤ Finset.univ.sum l.balances :=
          le_trans hAmt (single_le_sum l.balances src)
        omega
    }
  , by
      refine ⟨rfl, ?_, ?_⟩
      · -- newBal src = l.balances src - amt
        simp only [newBal, step1]
        rw [Function.update_of_ne hNeq, Function.update_self]
      · -- newBal dst = l.balances dst + amt
        simp only [newBal]
        exact Function.update_self dst _ _
  ⟩
