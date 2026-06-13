import Lemma.Scaled.Atoms.Transfer

open Scaled

variable {n : Nat} [NeZero n]

/-!
# Scaled Composition: Transfer then Transfer

Compose two transfers: A->B then B->C.

## Hypothesis
Both transfers are supply-neutral, so the composition should preserve total supply.
The second transfer's precondition (amt2 ≤ l1.balances b) should be bridgeable from
the first transfer's postcondition (l1.balances b = l.balances b + amt1) and the
user-supplied bound (amt2 ≤ l.balances b + amt1).

## Result: Tier 1 -- omega bridges postconditions to preconditions automatically
-/

def Scaled.transferThenTransfer
    (l : Ledger n) (a b c : Fin n)
    (amt1 amt2 : Nat)
    (hAmt1 : amt1 ≤ l.balances a)
    (hAB : a ≠ b) (hBC : b ≠ c) (_hAC : a ≠ c)
    (hAmt2 : amt2 ≤ l.balances b + amt1)
    : { l' : Ledger n // l'.totalSupply = l.totalSupply } :=
  let ⟨l1, h1supply, _h1srcBal, h1dstBal⟩ := Scaled.transfer l a b amt1 hAmt1 hAB
  let ⟨l2, h2supply, _, _⟩ := Scaled.transfer l1 b c amt2 (by omega) hBC
  ⟨l2, by omega⟩
