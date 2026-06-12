import Lemma.EVM.Asm
import Lemma.EVM.Proofs.OpSize

/-!
# assemble_length

The assembled output byte-length matches `asmSize`.

## Main result

`assemble_length`: if `EVM.assemble items = some bytes`, then
`bytes.length = EVM.asmSize items`.

## Strategy

We first prove an accumulator-invariant helper (`emit_length`) by induction
on the item list, then derive `assemble_length` by instantiating the
accumulator to `[]`.
-/

namespace EVM.Proofs

/-! ### Helpers -/

/-- Shifting the initial accumulator of `asmSize`'s underlying `foldl`. -/
private theorem foldl_add_init (items : List EVM.AsmItem) (a b : Nat) :
    List.foldl (fun acc item => acc + EVM.AsmItem.size item) (a + b) items =
    a + List.foldl (fun acc item => acc + EVM.AsmItem.size item) b items := by
  induction items generalizing a b with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp [List.foldl]
    rw [Nat.add_assoc]
    exact ih a (b + hd.size)

/-- `asmSize` distributes over cons: `asmSize (item :: rest) = item.size + asmSize rest`. -/
theorem asmSize_cons (item : EVM.AsmItem) (rest : List EVM.AsmItem) :
    EVM.asmSize (item :: rest) = item.size + EVM.asmSize rest := by
  unfold EVM.asmSize
  simp [List.foldl]
  exact foldl_add_init rest item.size 0

/-! ### Core accumulator invariant -/

/-- The accumulated output of `emit` has length `acc.length + asmSize items`. -/
theorem emit_length (labels : List (String × Nat)) (items : List EVM.AsmItem)
    (acc result : List UInt8) :
    EVM.assemble.emit labels items acc = some result →
    result.length = acc.length + EVM.asmSize items := by
  induction items generalizing acc result with
  | nil =>
    simp [EVM.assemble.emit, EVM.asmSize]
    intro h; rw [← h]
  | cons item rest ih =>
    intro h
    rw [asmSize_cons]
    unfold EVM.assemble.emit at h
    cases item with
    | label name =>
      simp at h
      simp [EVM.AsmItem.size]
      have := ih _ _ h
      rw [List.length_append] at this
      simp at this
      omega
    | op o =>
      simp at h
      simp [EVM.AsmItem.size]
      have := ih _ _ h
      rw [List.length_append, Op.toBytes_length] at this
      omega
    | pushLabelRef name =>
      simp at h
      simp [EVM.AsmItem.size] at h ⊢
      match hlookup : labels.lookup name with
      | some offset =>
        rw [hlookup] at h
        simp at h
        have := ih _ _ h
        rw [List.length_append] at this
        simp at this
        omega
      | none =>
        rw [hlookup] at h
        simp at h

/-! ### Main theorem -/

/-- If `assemble` succeeds, the output length equals `asmSize`. -/
theorem assemble_length (items : List EVM.AsmItem) (bytes : List UInt8) :
    EVM.assemble items = some bytes → bytes.length = EVM.asmSize items := by
  intro h
  unfold EVM.assemble at h
  have := emit_length (EVM.resolveLabels items) items [] bytes h
  simpa using this

end EVM.Proofs
