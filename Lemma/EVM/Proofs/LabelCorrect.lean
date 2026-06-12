import Lemma.EVM.Asm
import Lemma.EVM.Proofs.OpSize
import Lemma.EVM.Proofs.AsmSize
import Lemma.EVM.Proofs.LabelBound

/-!
# Label Correctness

Every label resolved by `resolveLabels` points to a JUMPDEST byte (`0x5b`) in the
assembled output, and every `pushLabelRef` emission places the resolved offset at
the expected position.

## Main results

* `label_points_to_jumpdest` (Theorem 4): if `resolveLabels` maps a label name to
  `offset`, then byte `offset` in the assembled output is `0x5b` (JUMPDEST).

* `pushLabelRef_uses_resolved_offset` (Theorem 5): when `emit` processes a
  `.pushLabelRef name` whose label resolves to `offset`, the two bytes emitted at
  the corresponding position are `0x60` (PUSH1) and `offset.toUInt8`.

## Strategy

Both proofs rest on two key helper lemmas:

1. **`emit_preserves_prefix`**: `emit` only appends to the accumulator, so all
   bytes at indices `< acc.length` are preserved in the final output.

2. **Synchronisation between `resolveLabels.go` and `emit`**: both traverse the
   item list computing the same byte offsets. When `go`'s offset counter equals
   `acc.length`, label positions recorded by `go` correspond exactly to positions
   where `emit` writes JUMPDEST bytes.
-/

namespace EVM.Proofs

/-! ### emit preserves prefix -/

/-- `emit` only appends to the accumulator — existing bytes are unchanged. -/
private theorem emit_preserves_prefix (labels : List (String × Nat))
    (items : List EVM.AsmItem) (acc result : List UInt8) (i : Nat)
    (h_emit : EVM.assemble.emit labels items acc = some result)
    (h_bound : i < acc.length) :
    result[i]? = acc[i]? := by
  induction items generalizing acc result with
  | nil =>
    unfold EVM.assemble.emit at h_emit
    simp at h_emit
    rw [h_emit]
  | cons item rest ih =>
    unfold EVM.assemble.emit at h_emit
    cases item with
    | label name =>
      simp at h_emit
      have h_bound' : i < (acc ++ [0x5b]).length := by
        rw [List.length_append]; simp; omega
      have := ih (acc ++ [0x5b]) result h_emit h_bound'
      rw [this, List.getElem?_append_left h_bound]
    | op o =>
      simp at h_emit
      have h_bound' : i < (acc ++ o.toBytes).length := by
        rw [List.length_append]; omega
      have := ih (acc ++ o.toBytes) result h_emit h_bound'
      rw [this, List.getElem?_append_left h_bound]
    | pushLabelRef name =>
      dsimp at h_emit
      match hlookup : labels.lookup name with
      | some offset =>
        rw [hlookup] at h_emit; simp at h_emit
        have h_bound' : i < (acc ++ [0x60, offset.toUInt8]).length := by
          rw [List.length_append]; simp; omega
        have := ih (acc ++ [0x60, offset.toUInt8]) result h_emit h_bound'
        rw [this, List.getElem?_append_left h_bound]
      | none =>
        rw [hlookup] at h_emit; simp at h_emit

/-! ### Synchronisation: go offset equals emit acc.length -/

/-- Core sync lemma: if `go` records `(name, v)` during traversal of `items`
    starting at offset `off`, and `emit` runs on the same `items` with an
    accumulator of length `off`, then `result[v]? = some 0x5b`.

    `h_not_acc` excludes entries inherited from the initial accumulator `goAcc`,
    ensuring `(name, v)` was recorded during this traversal. -/
private theorem emit_go_label_sync
    (labels : List (String × Nat))
    (items : List EVM.AsmItem) (off : Nat)
    (goAcc : List (String × Nat))
    (eacc : List UInt8) (result : List UInt8)
    (h_len : eacc.length = off)
    (h_emit : EVM.assemble.emit labels items eacc = some result)
    {name : String} {v : Nat}
    (h_mem : (name, v) ∈ EVM.resolveLabels.go items off goAcc)
    (h_not_acc : (name, v) ∉ goAcc) :
    result[v]? = some 0x5b := by
  induction items generalizing off goAcc eacc result with
  | nil =>
    unfold EVM.resolveLabels.go at h_mem
    rw [List.mem_reverse] at h_mem
    exact absurd h_mem h_not_acc
  | cons item rest ih =>
    unfold EVM.resolveLabels.go at h_mem
    unfold EVM.assemble.emit at h_emit
    cases item with
    | label lname =>
      simp at h_mem h_emit
      have h_len' : (eacc ++ [0x5b]).length = off + 1 := by
        rw [List.length_append]; simp; omega
      by_cases hmatch : (name, v) = (lname, off)
      · obtain ⟨_, hv⟩ := Prod.mk.inj hmatch
        subst hv
        have h_at : (eacc ++ [0x5b])[eacc.length]? = some 0x5b := by
          rw [List.getElem?_append_right (Nat.le_refl _)]; simp
        have h_bound : eacc.length < (eacc ++ [0x5b]).length := by
          rw [List.length_append]; simp
        rw [← h_len, emit_preserves_prefix labels rest (eacc ++ [0x5b]) result
          eacc.length h_emit h_bound, h_at]
      · have h_not_acc' : (name, v) ∉ ((lname, off) :: goAcc) := by
          intro h_in
          rw [List.mem_cons] at h_in
          rcases h_in with heq | hmem
          · exact hmatch heq
          · exact h_not_acc hmem
        exact ih (off + 1) ((lname, off) :: goAcc) (eacc ++ [0x5b]) result h_len'
          h_emit h_mem h_not_acc'
    | op o =>
      simp at h_emit
      have h_len' : (eacc ++ o.toBytes).length = off + o.size := by
        rw [List.length_append, Op.toBytes_length]; omega
      exact ih (off + o.size) goAcc (eacc ++ o.toBytes) result h_len' h_emit h_mem h_not_acc
    | pushLabelRef rname =>
      simp only [EVM.AsmItem.size] at h_mem
      dsimp at h_emit
      match hlookup : labels.lookup rname with
      | some offset =>
        rw [hlookup] at h_emit; simp at h_emit
        have h_len' : (eacc ++ [0x60, offset.toUInt8]).length = off + 2 := by
          rw [List.length_append]; simp; omega
        exact ih (off + 2) goAcc (eacc ++ [0x60, offset.toUInt8]) result h_len'
          h_emit h_mem h_not_acc
      | none =>
        rw [hlookup] at h_emit; simp at h_emit

/-! ### Theorem 4: label_points_to_jumpdest -/

/-- If `resolveLabels` maps label `name` to byte offset `offset`, then the
    assembled output has a JUMPDEST (`0x5b`) at that position. -/
theorem label_points_to_jumpdest (items : List EVM.AsmItem) (bytes : List UInt8)
    (name : String) (offset : Nat) :
    EVM.assemble items = some bytes →
    (EVM.resolveLabels items).lookup name = some offset →
    bytes[offset]? = some 0x5b := by
  intro h_asm h_lookup
  unfold EVM.assemble at h_asm
  have h_mem := lookup_some_mem h_lookup
  unfold EVM.resolveLabels at h_mem
  exact emit_go_label_sync (EVM.resolveLabels items) items 0 [] []
    bytes rfl h_asm h_mem List.not_mem_nil

/-! ### Theorem 5 helper: pushLabelRef emits resolved offset -/

/-- Accumulator-level lemma: when `emit` processes `pre ++ .pushLabelRef rname :: suf`,
    and `labels.lookup rname = some roffset`, the result bytes at positions
    `off + asmSize pre` and `off + asmSize pre + 1` are `0x60` and `roffset.toUInt8`. -/
private theorem emit_pushLabelRef_bytes
    (labels : List (String × Nat))
    (items : List EVM.AsmItem) (off : Nat)
    (eacc result : List UInt8)
    (h_len : eacc.length = off)
    (h_emit : EVM.assemble.emit labels items eacc = some result)
    (rname : String) (roffset : Nat)
    (h_lookup : labels.lookup rname = some roffset)
    (pre suf : List EVM.AsmItem)
    (h_items : items = pre ++ .pushLabelRef rname :: suf) :
    result[off + EVM.asmSize pre]? = some 0x60 ∧
    result[off + EVM.asmSize pre + 1]? = some roffset.toUInt8 := by
  induction pre generalizing items off eacc result with
  | nil =>
    simp at h_items; subst h_items
    unfold EVM.assemble.emit at h_emit
    dsimp at h_emit
    rw [h_lookup] at h_emit; simp at h_emit
    simp [EVM.asmSize]
    constructor
    · rw [← h_len]
      have h_at : (eacc ++ [0x60, roffset.toUInt8])[eacc.length]? = some 0x60 := by
        rw [List.getElem?_append_right (Nat.le_refl _)]; simp
      have h_bound : eacc.length < (eacc ++ [0x60, roffset.toUInt8]).length := by
        rw [List.length_append]; simp
      rw [emit_preserves_prefix labels suf _ result eacc.length h_emit h_bound, h_at]
    · rw [← h_len]
      have h_at : (eacc ++ [0x60, roffset.toUInt8])[eacc.length + 1]? =
          some roffset.toUInt8 := by
        rw [List.getElem?_append_right (by omega : eacc.length ≤ eacc.length + 1)]
        simp
      have h_bound : eacc.length + 1 < (eacc ++ [0x60, roffset.toUInt8]).length := by
        rw [List.length_append]; simp
      rw [emit_preserves_prefix labels suf _ result (eacc.length + 1) h_emit h_bound, h_at]
  | cons phd ptl ih =>
    simp at h_items; subst h_items
    unfold EVM.assemble.emit at h_emit
    rw [asmSize_cons]
    cases phd with
    | label lname =>
      simp at h_emit
      have h_len' : (eacc ++ [0x5b]).length = off + 1 := by
        rw [List.length_append]; simp; omega
      have hih := ih (ptl ++ .pushLabelRef rname :: suf) (off + 1)
        (eacc ++ [0x5b]) result h_len' h_emit rfl
      simp only [EVM.AsmItem.size, ← Nat.add_assoc]
      exact hih
    | op o =>
      simp at h_emit
      have h_len' : (eacc ++ o.toBytes).length = off + o.size := by
        rw [List.length_append, Op.toBytes_length]; omega
      have hih := ih (ptl ++ .pushLabelRef rname :: suf) (off + o.size)
        (eacc ++ o.toBytes) result h_len' h_emit rfl
      simp only [EVM.AsmItem.size, ← Nat.add_assoc]
      exact hih
    | pushLabelRef name2 =>
      dsimp at h_emit
      match hlookup2 : labels.lookup name2 with
      | some offset2 =>
        rw [hlookup2] at h_emit; simp at h_emit
        have h_len' : (eacc ++ [0x60, offset2.toUInt8]).length = off + 2 := by
          rw [List.length_append]; simp; omega
        have hih := ih (ptl ++ .pushLabelRef rname :: suf) (off + 2)
          (eacc ++ [0x60, offset2.toUInt8]) result h_len' h_emit rfl
        simp only [EVM.AsmItem.size, ← Nat.add_assoc]
        exact hih
      | none =>
        rw [hlookup2] at h_emit; simp at h_emit

/-! ### Theorem 5: pushLabelRef_uses_resolved_offset -/

/-- When the assembler processes a program containing `.pushLabelRef name` at
    item-list position `pre` (i.e. `items = pre ++ .pushLabelRef name :: suf`),
    and `resolveLabels` maps `name` to `offset`, the emitted bytes at byte
    position `asmSize pre` are `PUSH1` (`0x60`) followed by `offset.toUInt8`. -/
theorem pushLabelRef_uses_resolved_offset
    (items : List EVM.AsmItem) (bytes : List UInt8)
    (name : String) (offset : Nat)
    (pre suf : List EVM.AsmItem)
    (h_items : items = pre ++ .pushLabelRef name :: suf) :
    EVM.assemble items = some bytes →
    (EVM.resolveLabels items).lookup name = some offset →
    bytes[EVM.asmSize pre]? = some 0x60 ∧
    bytes[EVM.asmSize pre + 1]? = some offset.toUInt8 := by
  intro h_asm h_lookup
  unfold EVM.assemble at h_asm
  have h := emit_pushLabelRef_bytes (EVM.resolveLabels items) items 0 []
    bytes rfl h_asm name offset h_lookup pre suf h_items
  simp at h
  exact h

end EVM.Proofs
