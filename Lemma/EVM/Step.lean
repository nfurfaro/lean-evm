import Lemma.EVM.Decode

/-!
# EVM Single-Step Semantics

Executes one instruction, returning the new state or a halt result.
-/

namespace EVM

/-- Read 32 bytes from calldata at offset, zero-padded, big-endian → Nat. -/
def calldataWord (calldata : List UInt8) (offset : Nat) : Word :=
  (List.range 32).foldl (fun acc i =>
    let byte := match calldata[offset + i]? with
      | some b => UInt8.toNat b
      | none => 0
    acc + byte <<< (8 * (31 - i))) 0

/-- Execute one decoded instruction. -/
def step (code : List UInt8) (s : State) : StepResult :=
  match decode code s.pc with
  | none => .halt (.error "decode failed")
  | some (instr, nextPc) =>
    match instr with
    | .push1 v =>
      .continue { s with pc := nextPc, stack := UInt8.toNat v :: s.stack }
    | .push4 v =>
      .continue { s with pc := nextPc, stack := v :: s.stack }
    | .dup1 =>
      match s.stack with
      | a :: _ => .continue { s with pc := nextPc, stack := a :: s.stack }
      | _ => .halt (.error "stack underflow: dup1")
    | .dup2 =>
      match s.stack with
      | _ :: b :: _ => .continue { s with pc := nextPc, stack := b :: s.stack }
      | _ => .halt (.error "stack underflow: dup2")
    | .dup3 =>
      match s.stack with
      | _ :: _ :: c :: _ => .continue { s with pc := nextPc, stack := c :: s.stack }
      | _ => .halt (.error "stack underflow: dup3")
    | .swap1 =>
      match s.stack with
      | a :: b :: rest => .continue { s with pc := nextPc, stack := b :: a :: rest }
      | _ => .halt (.error "stack underflow: swap1")
    | .pop =>
      match s.stack with
      | _ :: rest => .continue { s with pc := nextPc, stack := rest }
      | _ => .halt (.error "stack underflow: pop")
    | .add =>
      match s.stack with
      | a :: b :: rest => .continue { s with pc := nextPc, stack := (a + b) :: rest }
      | _ => .halt (.error "stack underflow: add")
    | .sub =>
      match s.stack with
      | a :: b :: rest => .continue { s with pc := nextPc, stack := (a - b) :: rest }
      | _ => .halt (.error "stack underflow: sub")
    | .lt =>
      match s.stack with
      | a :: b :: rest =>
        let r := if a < b then 1 else 0
        .continue { s with pc := nextPc, stack := r :: rest }
      | _ => .halt (.error "stack underflow: lt")
    | .eq =>
      match s.stack with
      | a :: b :: rest =>
        let r := if a == b then 1 else 0
        .continue { s with pc := nextPc, stack := r :: rest }
      | _ => .halt (.error "stack underflow: eq")
    | .iszero =>
      match s.stack with
      | a :: rest =>
        let r := if a == 0 then 1 else 0
        .continue { s with pc := nextPc, stack := r :: rest }
      | _ => .halt (.error "stack underflow: iszero")
    | .shr =>
      match s.stack with
      | shift :: val :: rest =>
        .continue { s with pc := nextPc, stack := (val >>> shift) :: rest }
      | _ => .halt (.error "stack underflow: shr")
    | .sload =>
      match s.stack with
      | slot :: rest =>
        .continue { s with pc := nextPc, stack := s.storage slot :: rest }
      | _ => .halt (.error "stack underflow: sload")
    | .sstore =>
      match s.stack with
      | slot :: val :: rest =>
        .continue { s with
          pc := nextPc
          stack := rest
          storage := fun k => if k = slot then val else s.storage k }
      | _ => .halt (.error "stack underflow: sstore")
    | .mstore =>
      match s.stack with
      | offset :: val :: rest =>
        .continue { s with
          pc := nextPc
          stack := rest
          memory := writeMem s.memory offset val }
      | _ => .halt (.error "stack underflow: mstore")
    | .mload =>
      match s.stack with
      | offset :: rest =>
        let val := Bytes32.toWord (s.memory (offset / 32))
        .continue { s with pc := nextPc, stack := val :: rest }
      | _ => .halt (.error "stack underflow: mload")
    | .jump =>
      match s.stack with
      | dest :: rest => .continue { s with pc := dest, stack := rest }
      | _ => .halt (.error "stack underflow: jump")
    | .jumpi =>
      match s.stack with
      | dest :: cond :: rest =>
        let newPc := if cond != 0 then dest else nextPc
        .continue { s with pc := newPc, stack := rest }
      | _ => .halt (.error "stack underflow: jumpi")
    | .jumpdest =>
      .continue { s with pc := nextPc }
    | .stop =>
      .halt (.done s)
    | .ret =>
      match s.stack with
      | offset :: size :: _ =>
        let data := extractMemBytes s.memory offset size
        .halt (.returned data s)
      | _ => .halt (.error "stack underflow: ret")
    | .revert =>
      .halt .reverted
    | .sha3 =>
      match s.stack with
      | offset :: size :: rest =>
        let input := extractMemBytes s.memory offset size
        .continue { s with pc := nextPc, stack := keccak256 input :: rest }
      | _ => .halt (.error "stack underflow: sha3")
    | .caller =>
      .continue { s with pc := nextPc, stack := s.caller :: s.stack }
    | .calldataload =>
      match s.stack with
      | offset :: rest =>
        let val := calldataWord s.calldata offset
        .continue { s with pc := nextPc, stack := val :: rest }
      | _ => .halt (.error "stack underflow: calldataload")
    | .codecopy =>
      match s.stack with
      | _ :: _ :: _ :: rest =>
        .continue { s with pc := nextPc, stack := rest }
      | _ => .halt (.error "stack underflow: codecopy")

end EVM
