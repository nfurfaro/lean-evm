import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith

/-!
# Scaled ERC-20: Basic Definitions

Address type and helper lemmas for Finset.univ.sum with Function.update.
These replace the exhaustive Fin 3 case analysis from the PoC.
-/

variable {n : Nat}

/-- Split a Finset.univ sum to isolate one element (no subtraction, Nat-safe). -/
theorem sum_update_add [NeZero n] (f : Fin n → Nat) (i : Fin n) (amt : Nat) :
    Finset.univ.sum (Function.update f i (f i + amt)) = Finset.univ.sum f + amt := by
  have h1 := Finset.add_sum_erase Finset.univ (Function.update f i (f i + amt)) (Finset.mem_univ i)
  have h2 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
  simp only [Function.update_self] at h1
  have h3 : (Finset.univ.erase i).sum (Function.update f i (f i + amt)) =
      (Finset.univ.erase i).sum f :=
    Finset.sum_congr rfl (fun x hx => Function.update_of_ne (Finset.ne_of_mem_erase hx) _ _)
  rw [h3] at h1
  linarith

/-- Subtract from one element decreases the total sum (requires sufficient balance). -/
theorem sum_update_sub [NeZero n] (f : Fin n → Nat) (i : Fin n) (amt : Nat)
    (h : amt ≤ f i) :
    Finset.univ.sum (Function.update f i (f i - amt)) = Finset.univ.sum f - amt := by
  have h1 := Finset.add_sum_erase Finset.univ (Function.update f i (f i - amt)) (Finset.mem_univ i)
  have h2 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
  simp only [Function.update_self] at h1
  have h3 : (Finset.univ.erase i).sum (Function.update f i (f i - amt)) =
      (Finset.univ.erase i).sum f :=
    Finset.sum_congr rfl (fun x hx => Function.update_of_ne (Finset.ne_of_mem_erase hx) _ _)
  rw [h3] at h1
  have h4 : Finset.univ.sum (Function.update f i (f i - amt)) =
      f i - amt + (Finset.univ.erase i).sum f := by linarith
  have h5 : Finset.univ.sum f = f i + (Finset.univ.erase i).sum f := by linarith
  rw [h4, h5]
  omega

/-- Any single balance is ≤ the total sum. -/
theorem single_le_sum [NeZero n] (f : Fin n → Nat) (i : Fin n) :
    f i ≤ Finset.univ.sum f := by
  have h := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
  rw [← h]
  exact Nat.le_add_right _ _

/-- Subtract from one address, add to another: net sum unchanged. -/
theorem sum_update_sub_add [NeZero n] (f : Fin n → Nat) (i j : Fin n) (amt : Nat)
    (h_ne : i ≠ j) (h_le : amt ≤ f i) :
    Finset.univ.sum (Function.update (Function.update f i (f i - amt)) j (f j + amt))
      = Finset.univ.sum f := by
  have h1 : (Function.update f i (f i - amt)) j = f j :=
    Function.update_of_ne h_ne.symm _ _
  rw [← h1, sum_update_add, sum_update_sub _ _ _ h_le]
  have : amt ≤ Finset.univ.sum f := le_trans h_le (single_le_sum f i)
  omega
