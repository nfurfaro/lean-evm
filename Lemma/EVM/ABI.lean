/-!
# EVM ABI Constants (Solidity-compatible)

Function selectors and calldata offsets for ERC-20 operations.
Selectors are the first 4 bytes of keccak256 of the function signature.
-/

namespace EVM.ABI

/-- Selector for `mint(address,uint256)` = keccak256("mint(address,uint256)")[:4] -/
def mintSelector : UInt32 := 0x40c10f19

/-- Selector for `totalSupply()` = keccak256("totalSupply()")[:4] -/
def totalSupplySelector : UInt32 := 0x18160ddd

/-- Selector for `balanceOf(address)` = keccak256("balanceOf(address)")[:4] -/
def balanceOfSelector : UInt32 := 0x70a08231

/-- Selector for `transfer(address,uint256)` = keccak256("transfer(address,uint256)")[:4] -/
def transferSelector : UInt32 := 0xa9059cbb

/-- Calldata offset for first argument (after 4-byte selector). -/
def arg0Offset : UInt8 := 0x04

/-- Calldata offset for second argument. -/
def arg1Offset : UInt8 := 0x24

/-- Number of bits to right-shift calldata word to extract 4-byte selector. -/
def selectorShift : UInt8 := 0xe0

end EVM.ABI
