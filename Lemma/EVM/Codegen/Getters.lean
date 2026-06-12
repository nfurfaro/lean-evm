import Lemma.EVM.Op
import Lemma.EVM.Asm
import Lemma.EVM.Layout
import Lemma.EVM.ABI

namespace EVM.Codegen

open EVM

/--
Generate EVM opcodes for `totalSupply()`.
Loads slot 0 and returns it as a 32-byte word.
-/
def totalSupplyCode : List AsmItem :=
  [ .op (.push1 Layout.totalSupplySlot) -- [0]
  , .op .sload                          -- [supply]
  , .op (.push1 0x00)                   -- [0, supply]
  , .op .mstore                         -- []  mem[0x00]=supply
  , .op (.push1 0x20)                   -- [32]
  , .op (.push1 0x00)                   -- [0, 32]
  , .op .ret                            -- return mem[0x00..0x20]
  ]

/--
Generate EVM opcodes for `balanceOf(address)`.
Reads address from calldata, computes mapping slot, loads and returns.
-/
def balanceOfCode : List AsmItem :=
  -- Load address from calldata
  [ .op (.push1 ABI.arg0Offset)        -- [0x04]
  , .op .calldataload                   -- [addr]
  -- Compute mapping slot: keccak256(abi.encode(addr, 1))
  , .op (.push1 0x00)                   -- [0, addr]
  , .op .mstore                         -- []  mem[0x00]=addr
  , .op (.push1 Layout.balancesMappingSlot) -- [1]
  , .op (.push1 0x20)                   -- [0x20, 1]
  , .op .mstore                         -- []  mem[0x20]=1
  , .op (.push1 0x40)                   -- [0x40]
  , .op (.push1 0x00)                   -- [0, 0x40]
  , .op .sha3                           -- [bal_slot]
  -- Load and return
  , .op .sload                          -- [balance]
  , .op (.push1 0x00)                   -- [0, balance]
  , .op .mstore                         -- []  mem[0x00]=balance
  , .op (.push1 0x20)                   -- [32]
  , .op (.push1 0x00)                   -- [0, 32]
  , .op .ret                            -- return mem[0x00..0x20]
  ]

end EVM.Codegen
