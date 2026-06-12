import Lemma.EVM.State

/-!
# EVM Byte Decoding

Decode raw bytecode into structured instructions.
Given a bytecode list and PC, returns the decoded instruction and next PC.
-/

namespace EVM

/-- Decoded instruction (constructed from raw bytes, mirrors Op). -/
inductive Instr where
  | stop
  | add
  | sub
  | lt
  | eq
  | iszero
  | shr
  | sha3
  | caller
  | calldataload
  | pop
  | mload
  | mstore
  | sload
  | sstore
  | jump
  | jumpi
  | jumpdest
  | push1 (val : UInt8)
  | push4 (val : Nat)
  | dup1
  | dup2
  | dup3
  | swap1
  | ret
  | revert
  | codecopy
  deriving Repr, BEq

/-- Decode one instruction from bytecode at the given PC.
    Returns `(instruction, nextPC)` or `none` if decoding fails. -/
def decode (code : List UInt8) (pc : Nat) : Option (Instr × Nat) :=
  match code[pc]? with
  | none => none
  | some opByte =>
    match UInt8.toNat opByte with
    | 0x00 => some (.stop, pc + 1)
    | 0x01 => some (.add, pc + 1)
    | 0x03 => some (.sub, pc + 1)
    | 0x10 => some (.lt, pc + 1)
    | 0x14 => some (.eq, pc + 1)
    | 0x15 => some (.iszero, pc + 1)
    | 0x1c => some (.shr, pc + 1)
    | 0x20 => some (.sha3, pc + 1)
    | 0x33 => some (.caller, pc + 1)
    | 0x35 => some (.calldataload, pc + 1)
    | 0x39 => some (.codecopy, pc + 1)
    | 0x50 => some (.pop, pc + 1)
    | 0x51 => some (.mload, pc + 1)
    | 0x52 => some (.mstore, pc + 1)
    | 0x54 => some (.sload, pc + 1)
    | 0x55 => some (.sstore, pc + 1)
    | 0x56 => some (.jump, pc + 1)
    | 0x57 => some (.jumpi, pc + 1)
    | 0x5b => some (.jumpdest, pc + 1)
    | 0x60 =>
      match code[pc + 1]? with
      | none => none
      | some v => some (.push1 v, pc + 2)
    | 0x63 =>
      match code[pc + 1]?, code[pc + 2]?, code[pc + 3]?, code[pc + 4]? with
      | some b0, some b1, some b2, some b3 =>
        let val := UInt8.toNat b0 <<< 24 + UInt8.toNat b1 <<< 16 +
                   UInt8.toNat b2 <<< 8 + UInt8.toNat b3
        some (.push4 val, pc + 5)
      | _, _, _, _ => none
    | 0x80 => some (.dup1, pc + 1)
    | 0x81 => some (.dup2, pc + 1)
    | 0x82 => some (.dup3, pc + 1)
    | 0x90 => some (.swap1, pc + 1)
    | 0xf3 => some (.ret, pc + 1)
    | 0xfd => some (.revert, pc + 1)
    | _ => none

end EVM
