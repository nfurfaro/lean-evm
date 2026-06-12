import Lemma.EVM.Step

/-!
# EVM Execution Loop

Fuel-based bounded execution. Structurally terminating on `fuel : Nat`.
-/

namespace EVM

/-- Execute bytecode from a given state with bounded fuel.
    Each step consumes one unit of fuel. -/
def execute (code : List UInt8) (s : State) : Nat → Result
  | 0 => .error "out of fuel"
  | fuel + 1 =>
    match step code s with
    | .halt r => r
    | .continue s' => execute code s' fuel

end EVM
