import Lemma.EVM.Asm
import Lemma.EVM.Proofs.AsmSize

/-!
# resolveLabels_bound

Every label offset produced by `resolveLabels` is strictly less than `asmSize`.

## Strategy

We prove an accumulator invariant for `resolveLabels.go`: every pair `(name, v)`
that appears in the result either came from the initial accumulator or satisfies
`off ≤ v` and `v < off + asmSize items`. Then we instantiate with `off = 0`
and `acc = []`.

Since `go` returns `acc.reverse`, we work with membership (`∈`) rather than
`List.lookup` to avoid complications with lookup order after reversal.
We bridge from `List.lookup … = some v` to membership.
-/

namespace EVM.Proofs

/-! ### Lookup implies membership -/

theorem lookup_some_mem
    {l : List (String × Nat)} {k : String} {v : Nat} :
    l.lookup k = some v → (k, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup]
  | cons hd tl ih =>
    simp only [List.lookup]
    split <;> rename_i heq
    · intro h
      have hv := Option.some.inj h
      have hk : k = hd.fst := by rwa [beq_iff_eq] at heq
      have heq : (k, v) = hd := by
        ext <;> simp_all
      exact heq ▸ List.mem_cons_self
    · intro h
      exact List.mem_cons_of_mem _ (ih h)

/-! ### Key invariant for go -/

/-- Every entry in `go`'s result either came from `acc` or has its offset
    bounded by `off + asmSize items`. -/
private theorem go_mem_bound
    (items : List EVM.AsmItem) (off : Nat) (acc : List (String × Nat))
    {name : String} {v : Nat}
    (h : (name, v) ∈ EVM.resolveLabels.go items off acc) :
    (name, v) ∈ acc ∨ (off ≤ v ∧ v < off + EVM.asmSize items) := by
  induction items generalizing off acc with
  | nil =>
    unfold EVM.resolveLabels.go at h
    rw [List.mem_reverse] at h
    exact Or.inl h
  | cons item rest ih =>
    unfold EVM.resolveLabels.go at h
    rw [asmSize_cons]
    cases item with
    | label lname =>
      simp only at h
      have := @ih (off + 1) ((lname, off) :: acc) h
      cases this with
      | inl hmem =>
        rw [List.mem_cons] at hmem
        cases hmem with
        | inl heq =>
          right
          have := Prod.mk.inj heq
          obtain ⟨_, hv⟩ := this
          subst hv
          simp [EVM.AsmItem.size]
          omega
        | inr hacc =>
          exact Or.inl hacc
      | inr hbound =>
        right
        simp [EVM.AsmItem.size]
        omega
    | op o =>
      simp only at h
      have := @ih (off + o.size) acc h
      cases this with
      | inl hacc => exact Or.inl hacc
      | inr hbound =>
        right
        simp [EVM.AsmItem.size]
        omega
    | pushLabelRef rname =>
      simp only at h
      simp only [EVM.AsmItem.size] at h
      have := @ih (off + 2) acc h
      cases this with
      | inl hacc => exact Or.inl hacc
      | inr hbound =>
        right
        simp [EVM.AsmItem.size]
        omega

/-! ### Main theorem -/

theorem resolveLabels_bound (items : List EVM.AsmItem) (name : String) (offset : Nat) :
    (EVM.resolveLabels items).lookup name = some offset →
    offset < EVM.asmSize items := by
  intro hlookup
  have hmem := lookup_some_mem hlookup
  unfold EVM.resolveLabels at hmem
  have := go_mem_bound items 0 [] hmem
  cases this with
  | inl h =>
    simp [List.not_mem_nil] at h
  | inr h => omega

end EVM.Proofs
