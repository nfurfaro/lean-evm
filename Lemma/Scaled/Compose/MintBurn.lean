import Lemma.Scaled.Atoms.Mint
import Lemma.Scaled.Atoms.Burn

open Scaled

variable {n : Nat} [NeZero n]

/-!
# Scaled Composition: Mint then Burn (same address, same amount)

Mint `amt` tokens to `addr`, then burn `amt` tokens from `addr`.
The net effect should be supply-neutral.

## Result
**Tier 1** — no glue needed. `omega` closes both obligations:
  1. Burn precondition `amt ≤ l1.balances addr`: derived from
     `h1bal : l1.balances addr = l.balances addr + amt` (trivially ≥ amt).
  2. Supply neutrality `l2.totalSupply = l.totalSupply`: derived from
     `h1supply : l1.totalSupply = l.totalSupply + amt` and
     `h2supply : l2.totalSupply = l1.totalSupply - amt`,
     i.e. `(S + amt) - amt = S`.
-/

def Scaled.mintThenBurn
    (l : Ledger n) (addr : Fin n) (amt : Nat)
    : { l' : Ledger n // l'.totalSupply = l.totalSupply } :=
  let ⟨l1, h1supply, h1bal⟩ := Scaled.mint l addr amt
  let ⟨l2, h2supply, _⟩ := Scaled.burn l1 addr amt (by omega)
  ⟨l2, by omega⟩
