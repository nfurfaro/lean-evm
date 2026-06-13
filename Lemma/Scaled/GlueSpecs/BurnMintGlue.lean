import Lemma.Scaled.Basic
import Lemma.Scaled.Ledger

open Scaled

/-- Glue spec for burn→mint composition, extracted by `extract_glue_spec` tactic.
    Proves `amt ≤ l.totalSupply` from `amt ≤ l.balances src` using the Ledger invariant
    and `single_le_sum`. This is Tier 2: omega alone cannot close this goal. -/
theorem glue_spec_burnMint
    {n : ℕ}
    [NeZero n]
    (l : Ledger n)
    (src : Fin n)
    (_dst : Fin n)
    (amt : ℕ)
    (hAmt : amt ≤ l.balances src)
    (_l1 : Ledger n)
    (_h1supply : _l1.totalSupply = l.totalSupply - amt)
    (_h1bal : _l1.balances src = l.balances src - amt)
    (_l2 : Ledger n)
    (_h2supply : _l2.totalSupply = _l1.totalSupply + amt)
    (_h2bal : _l2.balances _dst = _l1.balances _dst + amt)
    : amt ≤ l.totalSupply := by
  rw [l.inv]
  exact le_trans hAmt (single_le_sum l.balances src)
