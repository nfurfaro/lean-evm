import Lemma.EVM.Op
import Lemma.EVM.Asm
import Lemma.EVM.Layout
import Lemma.EVM.ABI

namespace EVM.Codegen

open EVM

/--
Generate EVM opcodes for `mint(address, uint256)`.

Reads dst (arg0) and amt (arg1) from calldata.
Updates: balances[dst] += amt, totalSupply += amt.
Storage layout: Solidity-compatible (see Layout.lean).

Stack comments use notation: [top, next, ...]
-/
def mintCode : List AsmItem :=
  -- Load dst from calldata
  [ .op (.push1 ABI.arg0Offset)        -- [0x04]
  , .op .calldataload                   -- [dst]
  -- Load amt from calldata
  , .op (.push1 ABI.arg1Offset)        -- [0x24, dst]
  , .op .calldataload                   -- [amt, dst]

  -- === balances[dst] += amt ===
  -- Compute mapping slot: keccak256(abi.encode(dst, 1))
  -- Store dst at memory[0x00]
  , .op .dup2                           -- [dst, amt, dst]
  , .op (.push1 0x00)                   -- [0, dst, amt, dst]
  , .op .mstore                         -- [amt, dst]  mem[0x00]=dst
  -- Store mapping slot number at memory[0x20]
  , .op (.push1 Layout.balancesMappingSlot) -- [1, amt, dst]
  , .op (.push1 0x20)                   -- [0x20, 1, amt, dst]
  , .op .mstore                         -- [amt, dst]  mem[0x20]=1
  -- keccak256(mem[0x00..0x40])
  , .op (.push1 0x40)                   -- [0x40, amt, dst]
  , .op (.push1 0x00)                   -- [0, 0x40, amt, dst]
  , .op .sha3                           -- [bal_slot, amt, dst]
  -- Load current balance
  , .op .dup1                           -- [bal_slot, bal_slot, amt, dst]
  , .op .sload                          -- [old_bal, bal_slot, amt, dst]
  -- Add amt
  , .op .dup3                           -- [amt, old_bal, bal_slot, amt, dst]
  , .op .add                            -- [new_bal, bal_slot, amt, dst]
  -- Store new balance
  , .op .swap1                          -- [bal_slot, new_bal, amt, dst]
  , .op .sstore                         -- [amt, dst]

  -- === totalSupply += amt ===
  , .op (.push1 Layout.totalSupplySlot) -- [0, amt, dst]
  , .op .sload                          -- [old_supply, amt, dst]
  , .op .add                            -- [new_supply, dst]
  , .op (.push1 Layout.totalSupplySlot) -- [0, new_supply, dst]
  , .op .sstore                         -- [dst]

  -- Clean up and stop
  , .op .pop                            -- []
  , .op .stop
  ]

end EVM.Codegen
