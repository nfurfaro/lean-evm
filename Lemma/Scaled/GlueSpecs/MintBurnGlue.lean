import Lemma.Scaled.Ledger

open Scaled

/-- Glue spec for mint→burn composition, extracted by `extract_glue_spec` tactic.
    Proves that after minting `amt` to `addr`, the burn precondition `amt ≤ l1.balances addr`
    holds. -/
theorem glue_spec_mintBurn
    {n : ℕ}
    [NeZero n]
    (l : Ledger n)
    (addr : Fin n)
    (amt : ℕ)
    (l1 : Ledger n)
    (_h1supply : l1.totalSupply = l.totalSupply + amt)
    (h1bal : l1.balances addr = l.balances addr + amt)
    : amt ≤ l1.balances addr := by
  omega
