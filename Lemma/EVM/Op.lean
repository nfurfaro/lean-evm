/-!
# EVM Opcodes

Inductive type for the EVM opcode subset needed by the codegen.
Each variant maps to exactly one EVM opcode byte (+ immediate data).
-/

namespace EVM

/-- EVM opcodes used by the Lemma codegen. -/
inductive Op where
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
  | sload
  | sstore
  | jump
  | jumpi
  | mstore
  | mload
  | dup1
  | dup2
  | dup3
  | swap1
  | pop
  | push1 (val : UInt8)
  | push4 (val : UInt32)
  | jumpdest
  | revert
  | ret         -- RETURN (0xf3), named `ret` to avoid keyword clash
  | codecopy
  deriving Repr, BEq

/-- Size in bytes of an assembled opcode (opcode byte + immediate data). -/
def Op.size : Op → Nat
  | .push1 _  => 2
  | .push4 _  => 5
  | _ => 1

/-- Encode a single opcode to bytes. -/
def Op.toBytes : Op → List UInt8
  | .stop          => [0x00]
  | .add           => [0x01]
  | .sub           => [0x03]
  | .lt            => [0x10]
  | .eq            => [0x14]
  | .iszero        => [0x15]
  | .shr           => [0x1c]
  | .sha3          => [0x20]
  | .caller        => [0x33]
  | .calldataload  => [0x35]
  | .sload         => [0x54]
  | .sstore        => [0x55]
  | .jump          => [0x56]
  | .jumpi         => [0x57]
  | .mstore        => [0x52]
  | .mload         => [0x51]
  | .dup1          => [0x80]
  | .dup2          => [0x81]
  | .dup3          => [0x82]
  | .swap1         => [0x90]
  | .pop           => [0x50]
  | .push1 v       => [0x60, v]
  | .push4 v       =>
      let b0 := (v >>> 24).toUInt8
      let b1 := (v >>> 16).toUInt8
      let b2 := (v >>> 8).toUInt8
      let b3 := v.toUInt8
      [0x63, b0, b1, b2, b3]
  | .jumpdest      => [0x5b]
  | .revert        => [0xfd]
  | .ret           => [0xf3]
  | .codecopy      => [0x39]

end EVM
