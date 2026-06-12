/-!
# EVM Storage Layout (Solidity-compatible)

Slot assignments for an ERC-20 token contract.
-/

namespace EVM.Layout

/-- Storage slot for totalSupply. -/
def totalSupplySlot : UInt8 := 0

/-- Storage slot number for the balances mapping.
    Actual per-address slot = keccak256(abi.encode(address, balancesMappingSlot)). -/
def balancesMappingSlot : UInt8 := 1

end EVM.Layout
