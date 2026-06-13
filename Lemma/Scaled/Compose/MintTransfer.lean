import Lemma.Scaled.Atoms.Transfer
import Lemma.Scaled.Atoms.Mint

open Scaled

variable {n : Nat} [NeZero n]

/-!
# Scaled Composition: Mint then Transfer

Mint tokens to address A, then A transfers to B.

## Hypothesis
Mint increases supply by mintAmt; transfer preserves supply.
The composition's supply should be l.totalSupply + mintAmt.
The precondition bridge for the transfer needs the mint postcondition to
establish that A has enough balance.

## Result
**Tier 1** -- `omega` closes both the precondition and the final supply goal
after destructuring brings postcondition hypotheses into scope.

### Detail
- The transfer needs `transferAmt <= l1.balances a`.
- We know `l1.balances a = l.balances a + mintAmt` (postcondition `h1bal` from mint).
- We know `transferAmt <= l.balances a + mintAmt` (user precondition `hTransferAmt`).
- `omega` sees both and closes the precondition goal.
- The final supply goal `l2.totalSupply = l.totalSupply + mintAmt` follows from
  `h1supply : l1.totalSupply = l.totalSupply + mintAmt` and
  `h2supply : l2.totalSupply = l1.totalSupply`, which `omega` handles.

### Glue needed: None
`by omega` is sufficient for both goals.
-/

def Scaled.mintThenTransfer
    (l : Ledger n) (a b : Fin n)
    (mintAmt transferAmt : Nat)
    (hAB : a ≠ b)
    (hTransferAmt : transferAmt ≤ l.balances a + mintAmt)
    : { l' : Ledger n // l'.totalSupply = l.totalSupply + mintAmt } :=
  let ⟨l1, h1supply, h1bal⟩ := Scaled.mint l a mintAmt
  let ⟨l2, h2supply, _, _⟩ := Scaled.transfer l1 a b transferAmt (by omega) hAB
  ⟨l2, by omega⟩
