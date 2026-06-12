import Lemma.EVM.Op
import Lemma.EVM.Asm
import Lemma.EVM.Layout
import Lemma.EVM.ABI
import Lemma.EVM.Codegen.Mint
import Lemma.EVM.Codegen.Transfer
import Lemma.EVM.Codegen.Getters

namespace EVM.Codegen

open EVM

/--
Runtime bytecode: selector dispatch + function bodies.

Layout:
  1. Extract selector from calldata
  2. Compare against each known selector, jump to handler
  3. Fallback: revert
  4. Function bodies (mint, transfer, totalSupply, balanceOf)
-/
def runtimeCode : List AsmItem :=
  -- Extract function selector: calldata[0:4]
  -- Load first 32 bytes, shift right 224 bits to get top 4 bytes
  [ .op (.push1 0x00)                    -- [0]
  , .op .calldataload                    -- [calldata_word]
  , .op (.push1 ABI.selectorShift)       -- [224, calldata_word]
  , .op .shr                             -- [selector]

  -- Check mint(address,uint256) = 0x40c10f19
  , .op .dup1                            -- [selector, selector]
  , .op (.push4 ABI.mintSelector)        -- [0x40c10f19, selector, selector]
  , .op .eq                              -- [match?, selector]
  , .pushLabelRef "mint"                 -- [mint_addr, match?, selector]
  , .op .jumpi                           -- [selector]

  -- Check totalSupply() = 0x18160ddd
  , .op .dup1                            -- [selector, selector]
  , .op (.push4 ABI.totalSupplySelector) -- [0x18160ddd, selector, selector]
  , .op .eq                              -- [match?, selector]
  , .pushLabelRef "totalSupply"          -- [ts_addr, match?, selector]
  , .op .jumpi                           -- [selector]

  -- Check transfer(address,uint256) = 0xa9059cbb
  , .op .dup1                            -- [selector, selector]
  , .op (.push4 ABI.transferSelector)    -- [0xa9059cbb, selector, selector]
  , .op .eq                              -- [match?, selector]
  , .pushLabelRef "transfer"             -- [xfer_addr, match?, selector]
  , .op .jumpi                           -- [selector]

  -- Check balanceOf(address) = 0x70a08231
  , .op (.push4 ABI.balanceOfSelector)   -- [0x70a08231, selector]
  , .op .eq                              -- [match?]
  , .pushLabelRef "balanceOf"            -- [bo_addr, match?]
  , .op .jumpi                           -- []

  -- Fallback: revert
  , .op (.push1 0x00)                    -- [0]
  , .op (.push1 0x00)                    -- [0, 0]
  , .op .revert                          -- unreachable

  -- Function bodies
  , .label "mint"
  ] ++ mintCode ++ [
    .label "transfer"
  ] ++ transferCode ++ [
    .label "totalSupply"
  ] ++ totalSupplyCode ++ [
    .label "balanceOf"
  ] ++ balanceOfCode

/--
Deployment bytecode: copies runtime code to memory and returns it.
This is what you send as the `data` field of a contract creation transaction.
-/
def deployCode : Option ByteArray :=
  match assemble runtimeCode with
  | none => none
  | some runtimeBytes =>
    let runtimeSize := runtimeBytes.length.toUInt8
    -- The deploy preamble: CODECOPY runtime to memory, then RETURN it
    -- Preamble: PUSH1 size + PUSH1 offset + PUSH1 0 + CODECOPY + PUSH1 size + PUSH1 0 + RETURN
    -- = 2 + 2 + 2 + 1 + 2 + 2 + 1 = 12 bytes
    let preambleSize : UInt8 := 12
    let preamble : List UInt8 :=
      [ 0x60, runtimeSize                -- PUSH1 runtime_size
      , 0x60, preambleSize               -- PUSH1 runtime_offset (= preamble size)
      , 0x60, 0x00                       -- PUSH1 0x00
      , 0x39                             -- CODECOPY
      , 0x60, runtimeSize                -- PUSH1 runtime_size
      , 0x60, 0x00                       -- PUSH1 0x00
      , 0xf3                             -- RETURN
      ]
    some ⟨(preamble ++ runtimeBytes).toArray⟩

end EVM.Codegen
