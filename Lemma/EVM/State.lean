import Lemma.EVM.Op

/-!
# EVM Execution State

Machine state types for the EVM execution semantics.
Word type is `Nat` (matches Ledger specs; no overflow needed for totalSupply).
Memory is word-indexed (`Nat → Bytes32`) since all codegen memory ops are 32-byte aligned.
-/

namespace EVM

abbrev Word := Nat
abbrev Bytes32 := Fin 32 → UInt8

/-- Big-endian encoding: byte 0 is most significant. -/
def Word.toBytes32 (w : Word) : Bytes32 := fun i =>
  let shift := 8 * (31 - i.val)
  (w >>> shift).toUInt8

/-- Big-endian decoding: byte 0 is most significant. -/
def Bytes32.toWord (b : Bytes32) : Word :=
  Fin.foldl 32 (fun acc i => acc + (b i).toNat <<< (8 * (31 - i.val))) 0

/-- Convert a word to a 32-element byte list (big-endian). -/
def wordToBytes (w : Word) : List UInt8 :=
  (List.range 32).map fun i =>
    let shift := 8 * (31 - i)
    (w >>> shift).toUInt8

/-- EVM machine state. -/
structure State where
  pc : Nat
  stack : List Word
  memory : Nat → Bytes32
  storage : Nat → Word
  calldata : List UInt8
  caller : Word := 0

/-- Default memory: all zeros. -/
def Memory.default : Nat → Bytes32 := fun _ _ => 0

/-- Initial state with given storage. -/
def State.init (storage : Nat → Word) : State where
  pc := 0
  stack := []
  memory := Memory.default
  storage := storage
  calldata := []
  caller := 0

/-- Execution result. -/
inductive Result where
  | done (s : State)
  | returned (data : List UInt8) (s : State)
  | reverted
  | error (msg : String)

/-- Single-step result. -/
inductive StepResult where
  | continue (s : State)
  | halt (r : Result)

/-- Write a 32-byte word to memory at the given byte offset (must be 32-aligned). -/
def writeMem (mem : Nat → Bytes32) (byteOffset : Nat) (val : Word) : Nat → Bytes32 :=
  fun idx => if idx = byteOffset / 32 then Word.toBytes32 val else mem idx

/-- Extract `len` bytes from memory starting at `byteOffset`. -/
def extractMemBytes (mem : Nat → Bytes32) (byteOffset : Nat) (len : Nat) : List UInt8 :=
  (List.range len).map fun i =>
    let absOffset := byteOffset + i
    let wordIdx := absOffset / 32
    let byteIdx := absOffset % 32
    mem wordIdx ⟨byteIdx, by omega⟩

/-- Keccak256 hash function (axiomatized). -/
opaque keccak256 (input : List UInt8) : Nat

end EVM
