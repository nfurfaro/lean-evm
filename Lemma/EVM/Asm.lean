import Lemma.EVM.Op

namespace EVM

/-- An assembly item: opcode, label (emits JUMPDEST), or a push-label reference. -/
inductive AsmItem where
  | op (o : Op)
  | label (name : String)
  | pushLabelRef (name : String)   -- emits PUSH1 <resolved offset>
  deriving Repr, BEq

/-- Byte size of an assembly item. -/
def AsmItem.size : AsmItem → Nat
  | .op o          => o.size
  | .label _       => 1    -- JUMPDEST
  | .pushLabelRef _ => 2   -- PUSH1 + 1 byte offset

/-- Resolve all label names to byte offsets. -/
def resolveLabels (items : List AsmItem) : List (String × Nat) :=
  let rec go (items : List AsmItem) (offset : Nat) (acc : List (String × Nat))
      : List (String × Nat) :=
    match items with
    | [] => acc.reverse
    | item :: rest =>
      match item with
      | .label name => go rest (offset + 1) ((name, offset) :: acc)
      | _ => go rest (offset + item.size) acc
  go items 0 []

/-- Assemble items into a `List UInt8`. Returns none if a label reference is unresolved. -/
def assemble (items : List AsmItem) : Option (List UInt8) :=
  let labels := resolveLabels items
  let rec emit (items : List AsmItem) (acc : List UInt8) : Option (List UInt8) :=
    match items with
    | [] => some acc
    | item :: rest =>
      match item with
      | .label _ => emit rest (acc ++ [0x5b])  -- JUMPDEST
      | .op o =>
        let acc := acc ++ o.toBytes
        emit rest acc
      | .pushLabelRef name =>
        match labels.lookup name with
        | some offset => emit rest (acc ++ [0x60, offset.toUInt8])
        | none => none
  emit items []

/-- Assemble items into a `ByteArray`. Wrapper around `assemble` for consumers needing bytes. -/
def assembleBytes (items : List AsmItem) : Option ByteArray :=
  (assemble items).map fun bs => ⟨bs.toArray⟩

/-- Total byte size of assembled output. -/
def asmSize (items : List AsmItem) : Nat :=
  items.foldl (fun acc item => acc + item.size) 0

end EVM
