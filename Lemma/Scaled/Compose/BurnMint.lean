import Lemma.Scaled.Atoms.Burn
import Lemma.Scaled.Atoms.Mint

open Scaled

variable {n : Nat} [NeZero n]

/-!
# Scaled Composition: Burn then Mint

Burn `amt` tokens from `src`, then mint `amt` tokens to `dst`.
Net effect: totalSupply is preserved (burn subtracts, mint adds back the same amount).

## Tier Classification: Tier 2

**omega alone fails.** The burn postcondition gives `l1.totalSupply = l.totalSupply - amt`
and mint gives `l2.totalSupply = l1.totalSupply + amt`. For omega to close the goal
`l2.totalSupply = l.totalSupply`, it needs `l.totalSupply - amt + amt = l.totalSupply`,
which requires `amt ≤ l.totalSupply` (Nat subtraction truncates at 0). The hypothesis
only provides `amt ≤ l.balances src`, so the bridge from balance to supply is needed.

### Glue: 2 lines (vs PoC's 4 lines)
- `rw [l.inv]` rewrites `l.totalSupply` to `Finset.univ.sum l.balances`
- `exact le_trans hAmt (single_le_sum l.balances src)` chains the balance bound
  through `single_le_sum` to get `amt ≤ sum`.

### PoC comparison
The PoC (Fin 3) required exhaustive case matching on all 3 constructors of `Fin 3`:
```
match src, hAmt with
| ⟨0, _⟩, hAmt => simp at hAmt; omega
| ⟨1, _⟩, hAmt => simp at hAmt; omega
| ⟨2, _⟩, hAmt => simp at hAmt; omega
```
This was 4 lines and would scale linearly with `n` (O(n) match arms).

The scaled version uses `single_le_sum` (a general lemma for `Fin n`) which gives
`f i ≤ Finset.univ.sum f` in one step. Combined with `le_trans` and `l.inv`, the
entire glue is 2 lines and works for any `n`. This confirms the prediction that
Mathlib's `Finset.sum` lemmas cleanly replace exhaustive case analysis.

### Verdict
- **Tier 2 confirmed** (as predicted) -- omega cannot derive `amt ≤ totalSupply`
  from `amt ≤ balances src` without the invariant bridge.
- **Glue reduced** from 4 lines (PoC) to 2 lines (scaled), and now works for
  arbitrary `n` instead of only `Fin 3`.
- **Key lemma:** `single_le_sum` replaces the exhaustive `Fin 3` case match.
-/

def Scaled.burnThenMint
    (l : Ledger n) (src dst : Fin n) (amt : Nat)
    (hAmt : amt ≤ l.balances src)
    : { l' : Ledger n // l'.totalSupply = l.totalSupply } :=
  let ⟨l1, h1supply, _⟩ := Scaled.burn l src amt hAmt
  let ⟨l2, h2supply, _⟩ := Scaled.mint l1 dst amt
  have hSupplyGeSrc : amt ≤ l.totalSupply := by
    rw [l.inv]
    exact le_trans hAmt (single_le_sum l.balances src)
  ⟨l2, by omega⟩
