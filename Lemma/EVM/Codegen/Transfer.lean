import Lemma.EVM.Op
import Lemma.EVM.Asm
import Lemma.EVM.Layout
import Lemma.EVM.ABI

namespace EVM.Codegen

open EVM

/--
Generate EVM opcodes for `transfer(address, uint256)`.

Reads src from CALLER (msg.sender), dst (arg0) and amt (arg1) from calldata.
Checks `balances[src] >= amt`, reverts if not.
Updates: `balances[src] -= amt`, `balances[dst] += amt`.
totalSupply is unchanged.

Stack comments use notation: [top, next, ...]
-/
def transferCode : List AsmItem :=
  -- === Load arguments ===
  [ .op .caller                            -- [src]
  , .op (.push1 ABI.arg0Offset)           -- [0x04, src]
  , .op .calldataload                      -- [dst, src]
  , .op (.push1 ABI.arg1Offset)           -- [0x24, dst, src]
  , .op .calldataload                      -- [amt, dst, src]

  -- === Compute src balance slot: keccak256(abi.encode(src, 1)) ===
  , .op .dup3                              -- [src, amt, dst, src]
  , .op (.push1 0x00)                      -- [0, src, amt, dst, src]
  , .op .mstore                            -- [amt, dst, src]          mem[0]=src
  , .op (.push1 Layout.balancesMappingSlot) -- [1, amt, dst, src]
  , .op (.push1 0x20)                      -- [0x20, 1, amt, dst, src]
  , .op .mstore                            -- [amt, dst, src]          mem[0x20]=1
  , .op (.push1 0x40)                      -- [0x40, amt, dst, src]
  , .op (.push1 0x00)                      -- [0, 0x40, amt, dst, src]
  , .op .sha3                              -- [src_slot, amt, dst, src]

  -- === Load src balance and check ===
  , .op .dup1                              -- [src_slot, src_slot, amt, dst, src]
  , .op .sload                             -- [src_bal, src_slot, amt, dst, src]
  -- Check: src_bal >= amt? Revert if src_bal < amt.
  -- We need [src_bal, amt, ...] for LT to give (src_bal < amt).
  , .op .dup3                              -- [amt, src_bal, src_slot, amt, dst, src]
  , .op .dup2                              -- [src_bal, amt, src_bal, src_slot, amt, dst, src]
  , .op .lt                                -- [src_bal<amt?, src_bal, src_slot, amt, dst, src]
  , .op .iszero                            -- [src_bal>=amt?, src_bal, src_slot, amt, dst, src]
  , .pushLabelRef "ok"                     -- [ok_addr, src_bal>=amt?, src_bal, ...]
  , .op .jumpi                             -- [src_bal, src_slot, amt, dst, src]  (jumped if ok)
  -- Revert path (insufficient balance)
  , .op (.push1 0x00)                      -- [0]
  , .op (.push1 0x00)                      -- [0, 0]
  , .op .revert                            -- halt

  -- === Success path ===
  , .label "ok"                            -- JUMPDEST; stack: [src_bal, src_slot, amt, dst, src]

  -- === Update src balance: balances[src] -= amt ===
  , .op .dup3                              -- [amt, src_bal, src_slot, amt, dst, src]
  , .op .swap1                             -- [src_bal, amt, src_slot, amt, dst, src]
  , .op .sub                               -- [src_bal-amt, src_slot, amt, dst, src]
  , .op .swap1                             -- [src_slot, src_bal-amt, amt, dst, src]
  , .op .sstore                            -- [amt, dst, src]

  -- === Compute dst balance slot: keccak256(abi.encode(dst, 1)) ===
  -- mem[0x20]=1 still valid from src computation
  , .op .dup2                              -- [dst, amt, dst, src]
  , .op (.push1 0x00)                      -- [0, dst, amt, dst, src]
  , .op .mstore                            -- [amt, dst, src]          mem[0]=dst
  , .op (.push1 0x40)                      -- [0x40, amt, dst, src]
  , .op (.push1 0x00)                      -- [0, 0x40, amt, dst, src]
  , .op .sha3                              -- [dst_slot, amt, dst, src]

  -- === Update dst balance: balances[dst] += amt ===
  , .op .dup1                              -- [dst_slot, dst_slot, amt, dst, src]
  , .op .sload                             -- [dst_bal, dst_slot, amt, dst, src]
  , .op .dup3                              -- [amt, dst_bal, dst_slot, amt, dst, src]
  , .op .add                               -- [dst_bal+amt, dst_slot, amt, dst, src]
  , .op .swap1                             -- [dst_slot, dst_bal+amt, amt, dst, src]
  , .op .sstore                            -- [amt, dst, src]

  -- === Clean up and stop ===
  , .op .pop                               -- [dst, src]
  , .op .pop                               -- [src]
  , .op .pop                               -- []
  , .op .stop
  ]

end EVM.Codegen
