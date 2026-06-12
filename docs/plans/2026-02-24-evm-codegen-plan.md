# EVM Bytecode Codegen Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Generate Solidity-ABI-compatible EVM bytecode from the mint spec — deployable to anvil, callable with cast.

**Architecture:** Pure Lean functions organized as Op (inductive) → Asm (assembler) → Codegen (per-function opcode lists) → Contract (dispatch + deploy wrapper). No IO, no MetaM — everything is pure so it's on the path to formal verification.

**Tech Stack:** Lean 4 (no new dependencies), Foundry (anvil + cast) for testing.

**Design doc:** `docs/plans/2026-02-24-evm-codegen-design.md`

**Project root:** `/Users/nick/dev/essential/lemma`
**Build command:** `~/.elan/bin/lake build`
**VCS:** jj (Jujutsu) — NOT git. Use `jj commit -m "msg"` to commit, `jj status` to check status.

---

## Task 1: EVM Opcode Type

**Files:**
- Create: `Lemma/EVM/Op.lean`

**Step 1: Create the opcode inductive type and byte encoding**

```lean
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
  | eq
  | shr
  | sha3
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
  | .eq            => [0x14]
  | .shr           => [0x1c]
  | .sha3          => [0x20]
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
```

**Step 2: Verify it compiles**

Run: `~/.elan/bin/lake build Lemma.EVM.Op`
Expected: Build succeeds with no errors.

**Step 3: Commit**

```bash
jj commit -m "feat(evm): opcode inductive type with byte encoding"
```

---

## Task 2: Assembler

**Files:**
- Create: `Lemma/EVM/Asm.lean`

The assembler takes a list of `Op` and produces a `ByteArray`. It also supports **labels** — named jump targets that get resolved to byte offsets. Labels are needed because when we emit `PUSH1 <offset>; JUMP`, we don't know the offset until all preceding opcodes are measured.

We model labels as a separate type interleaved with ops:

**Step 1: Create the assembler**

```lean
import Lemma.EVM.Op

namespace EVM

/-- An assembly item is either an opcode or a label (jump target). -/
inductive AsmItem where
  | op (o : Op)
  | label (name : String)
  deriving Repr, BEq

/-- A forward reference — a PUSH1 whose byte needs to be patched with a label's offset. -/
structure Fixup where
  offset : Nat      -- byte position of the PUSH1's immediate byte
  label : String

/-- Measure the byte size of an assembly item. -/
def AsmItem.size : AsmItem → Nat
  | .op o    => o.size
  | .label _ => 0  -- labels emit no bytes

/-- First pass: compute byte offset for each label. -/
def resolveLabels (items : List AsmItem) : List (String × Nat) :=
  let rec go (items : List AsmItem) (offset : Nat) (acc : List (String × Nat))
      : List (String × Nat) :=
    match items with
    | [] => acc.reverse
    | .label name :: rest => go rest offset ((name, offset) :: acc)
    | .op o :: rest       => go rest (offset + o.size) acc
  go items 0 []

/-- Look up a label's byte offset. -/
def findLabel (labels : List (String × Nat)) (name : String) : Option Nat :=
  labels.lookup name

/-- Assemble a list of items into a ByteArray.
    Labels become JUMPDESTs (1 byte). Forward references in PUSH1 are patched.
    Returns none if a label is unresolved. -/
def assemble (items : List AsmItem) : Option ByteArray :=
  -- Labels emit a JUMPDEST byte, so re-measure including them
  let rec measure (items : List AsmItem) (offset : Nat) (acc : List (String × Nat))
      : List (String × Nat) :=
    match items with
    | [] => acc.reverse
    | .label name :: rest => measure rest (offset + 1) ((name, offset) :: acc)  -- JUMPDEST = 1 byte
    | .op o :: rest       => measure rest (offset + o.size) acc
  let labels := measure items 0 []
  let rec emit (items : List AsmItem) (acc : ByteArray) : Option ByteArray :=
    match items with
    | [] => some acc
    | .label _ :: rest => emit rest (acc.push 0x5b)  -- JUMPDEST
    | .op o :: rest =>
      let bytes := o.toBytes
      let acc := bytes.foldl (fun a b => a.push b) acc
      emit rest acc
  emit items ByteArray.empty

/-- Total byte size of assembled items (including JUMPDEST for labels). -/
def asmSize (items : List AsmItem) : Nat :=
  items.foldl (fun acc item =>
    match item with
    | .op o    => acc + o.size
    | .label _ => acc + 1  -- JUMPDEST
  ) 0

/-- Helper: wrap an Op as an AsmItem. -/
def op (o : Op) : AsmItem := .op o

/-- Helper: create a label AsmItem. -/
def label (name : String) : AsmItem := .label name

/-- Helper: PUSH1 targeting a named label. The caller is responsible for ensuring
    the label resolves to a value that fits in UInt8 (< 256 bytes of bytecode). -/
def pushLabel (labels : List (String × Nat)) (name : String) : Op :=
  match findLabel labels name with
  | some offset => .push1 offset.toUInt8
  | none        => .push1 0  -- fallback; should not happen in well-formed code

end EVM
```

Wait — there's a chicken-and-egg problem. `pushLabel` needs resolved labels, but labels are resolved from the item list that contains the pushes. We need a two-pass approach: first pass resolves labels, second pass emits bytes using resolved offsets.

Let me restructure. The codegen will produce items using a placeholder, and the assembler resolves in two passes:

```lean
import Lemma.EVM.Op

namespace EVM

/-- An assembly item: opcode, label (emits JUMPDEST), or a push-label reference. -/
inductive AsmItem where
  | op (o : Op)
  | label (name : String)
  | pushLabelRef (name : String)   -- emits PUSH1 <resolved offset>
  deriving Repr, BEq

/-- Byte size of an assembly item. -/
def AsmItem.size : AsmItem → Nat
  | .op o          => o.size
  | .label _       => 1    -- JUMPDEST
  | .pushLabelRef _ => 2   -- PUSH1 + 1 byte offset

/-- Resolve all label names to byte offsets. -/
def resolveLabels (items : List AsmItem) : List (String × Nat) :=
  let rec go (items : List AsmItem) (offset : Nat) (acc : List (String × Nat))
      : List (String × Nat) :=
    match items with
    | [] => acc.reverse
    | item :: rest =>
      match item with
      | .label name => go rest (offset + 1) ((name, offset) :: acc)
      | _ => go rest (offset + item.size) acc
  go items 0 []

/-- Assemble items into a ByteArray. Returns none if a label reference is unresolved. -/
def assemble (items : List AsmItem) : Option ByteArray :=
  let labels := resolveLabels items
  let rec emit (items : List AsmItem) (acc : ByteArray) : Option ByteArray :=
    match items with
    | [] => some acc
    | item :: rest =>
      match item with
      | .label _ => emit rest (acc.push 0x5b)  -- JUMPDEST
      | .op o =>
        let acc := o.toBytes.foldl (fun a b => a.push b) acc
        emit rest acc
      | .pushLabelRef name =>
        match labels.lookup name with
        | some offset => emit rest ((acc.push 0x60).push offset.toUInt8)
        | none => none
  emit items ByteArray.empty

/-- Total byte size of assembled output. -/
def asmSize (items : List AsmItem) : Nat :=
  items.foldl (fun acc item => acc + item.size) 0

end EVM
```

**Step 2: Verify it compiles**

Run: `~/.elan/bin/lake build Lemma.EVM.Asm`
Expected: Build succeeds.

**Step 3: Commit**

```bash
jj commit -m "feat(evm): assembler — label resolution and List AsmItem → ByteArray"
```

---

## Task 3: Storage Layout and ABI Constants

**Files:**
- Create: `Lemma/EVM/Layout.lean`
- Create: `Lemma/EVM/ABI.lean`

**Step 1: Create storage layout definitions**

```lean
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
```

**Step 2: Create ABI definitions**

```lean
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

/-- Calldata offset for first argument (after 4-byte selector). -/
def arg0Offset : UInt8 := 0x04

/-- Calldata offset for second argument. -/
def arg1Offset : UInt8 := 0x24

/-- Number of bits to right-shift calldata word to extract 4-byte selector. -/
def selectorShift : UInt8 := 0xe0

end EVM.ABI
```

**Step 3: Verify both compile**

Run: `~/.elan/bin/lake build Lemma.EVM.Layout Lemma.EVM.ABI`
Expected: Build succeeds.

**Step 4: Commit**

```bash
jj commit -m "feat(evm): storage layout and ABI constant definitions"
```

---

## Task 4: Mint Codegen

**Files:**
- Create: `Lemma/EVM/Codegen/Mint.lean`

This is the core of the sprint. The function produces the opcode sequence for `mint(address, uint256)`.

**Step 1: Create the mint codegen**

```lean
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
```

**Step 2: Verify it compiles**

Run: `~/.elan/bin/lake build Lemma.EVM.Codegen.Mint`
Expected: Build succeeds.

**Step 3: Commit**

```bash
jj commit -m "feat(evm): mint codegen — opcode sequence for mint(address,uint256)"
```

---

## Task 5: Getter Codegen

**Files:**
- Create: `Lemma/EVM/Codegen/Getters.lean`

Two getter functions: `totalSupply()` and `balanceOf(address)`.

**Step 1: Create the getter codegen**

```lean
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
```

**Step 2: Verify it compiles**

Run: `~/.elan/bin/lake build Lemma.EVM.Codegen.Getters`
Expected: Build succeeds.

**Step 3: Commit**

```bash
jj commit -m "feat(evm): getter codegen — totalSupply() and balanceOf(address)"
```

---

## Task 6: Contract Assembly (Dispatch + Deploy)

**Files:**
- Create: `Lemma/EVM/Codegen/Contract.lean`

This combines the selector dispatch, all three function bodies, and the deployment wrapper.

**Step 1: Create the contract assembler**

```lean
import Lemma.EVM.Op
import Lemma.EVM.Asm
import Lemma.EVM.Layout
import Lemma.EVM.ABI
import Lemma.EVM.Codegen.Mint
import Lemma.EVM.Codegen.Getters

namespace EVM.Codegen

open EVM

/--
Runtime bytecode: selector dispatch + function bodies.

Layout:
  1. Extract selector from calldata
  2. Compare against each known selector, jump to handler
  3. Fallback: revert
  4. Function bodies (mint, totalSupply, balanceOf)
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
    let runtimeSize := runtimeBytes.size
    -- The deploy preamble: CODECOPY runtime to memory, then RETURN it
    -- We need to know the preamble size to compute the runtime offset
    -- Preamble: PUSH1 size + PUSH1 offset + PUSH1 0 + CODECOPY + PUSH1 size + PUSH1 0 + RETURN
    -- = 2 + 2 + 2 + 1 + 2 + 2 + 1 = 12 bytes (if size fits in PUSH1)
    let preambleSize : UInt8 := 12
    let preamble : List UInt8 :=
      [ 0x60, runtimeSize.toUInt8        -- PUSH1 runtime_size
      , 0x60, preambleSize               -- PUSH1 runtime_offset (= preamble size)
      , 0x60, 0x00                       -- PUSH1 0x00
      , 0x39                             -- CODECOPY
      , 0x60, runtimeSize.toUInt8        -- PUSH1 runtime_size
      , 0x60, 0x00                       -- PUSH1 0x00
      , 0xf3                             -- RETURN
      ]
    let mut result := ByteArray.empty
    for b in preamble do
      result := result.push b
    some (result ++ runtimeBytes)

end EVM.Codegen
```

**Step 2: Verify it compiles**

Run: `~/.elan/bin/lake build Lemma.EVM.Codegen.Contract`
Expected: Build succeeds.

**Step 3: Commit**

```bash
jj commit -m "feat(evm): contract assembly — dispatch + deploy wrapper"
```

---

## Task 7: Hex Output

**Files:**
- Create: `Lemma/EVM/Hex.lean`

**Step 1: Create hex output utility and #eval**

```lean
import Lemma.EVM.Codegen.Contract

namespace EVM

/-- Convert a byte to its 2-character hex representation. -/
def byteToHex (b : UInt8) : String :=
  let hi := b >>> 4
  let lo := b &&& 0x0f
  let hexChar (n : UInt8) : Char :=
    if n < 10 then Char.ofNat (48 + n.toNat)   -- '0'..'9'
    else Char.ofNat (87 + n.toNat)              -- 'a'..'f'
  ⟨[hexChar hi, hexChar lo]⟩

/-- Convert a ByteArray to a hex string (no 0x prefix). -/
def bytesToHex (bs : ByteArray) : String :=
  bs.foldl (fun acc b => acc ++ byteToHex b) ""

/-- The full deployment bytecode as a hex string. -/
def deployHex : Option String :=
  Codegen.deployCode.map (fun bs => "0x" ++ bytesToHex bs)

end EVM

-- Print the deployable bytecode
#eval do
  match EVM.deployHex with
  | some hex => IO.println hex
  | none     => IO.println "ERROR: label resolution failed"
```

**Step 2: Verify it compiles and produces hex output**

Run: `~/.elan/bin/lake build Lemma.EVM.Hex`
Expected: Build succeeds. The `#eval` should print a hex string starting with `0x60...`.

**Step 3: Commit**

```bash
jj commit -m "feat(evm): hex output — #eval prints deployable bytecode"
```

---

## Task 8: Wire Up Imports

**Files:**
- Modify: `Lemma.lean` — add imports for all new EVM modules

**Step 1: Add imports to root file**

Add these lines at the end of `/Users/nick/dev/essential/lemma/Lemma.lean`:

```lean
import Lemma.EVM.Op
import Lemma.EVM.Asm
import Lemma.EVM.Layout
import Lemma.EVM.ABI
import Lemma.EVM.Codegen.Mint
import Lemma.EVM.Codegen.Getters
import Lemma.EVM.Codegen.Contract
import Lemma.EVM.Hex
```

**Step 2: Full build**

Run: `~/.elan/bin/lake build`
Expected: Full project builds with no errors.

**Step 3: Commit**

```bash
jj commit -m "feat(evm): wire up imports for EVM codegen modules"
```

---

## Task 9: End-to-End Test with Foundry

**Prerequisites:** Foundry installed (`anvil`, `cast`). If not: `curl -L https://foundry.paradigm.xyz | bash && foundryup`.

This task tests the generated bytecode against a real EVM.

**Step 1: Get the hex output**

Run the Lean build and capture the hex string from the `#eval` in `Hex.lean`. Copy it.

**Step 2: Start anvil**

```bash
anvil &
```

Default RPC: `http://127.0.0.1:8545`
Default account: `0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266` (private key: `0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80`)

**Step 3: Deploy the contract**

```bash
cast send --rpc-url http://127.0.0.1:8545 \
  --private-key 0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80 \
  --create 0x<HEX_FROM_STEP_1>
```

Expected: Transaction receipt with a `contractAddress` field. Save this address.

**Step 4: Call mint**

```bash
cast send --rpc-url http://127.0.0.1:8545 \
  --private-key 0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80 \
  <CONTRACT_ADDR> "mint(address,uint256)" \
  0x000000000000000000000000000000000000dead 100
```

**Step 5: Verify totalSupply**

```bash
cast call --rpc-url http://127.0.0.1:8545 \
  <CONTRACT_ADDR> "totalSupply()(uint256)"
```

Expected: `100`

**Step 6: Verify balanceOf**

```bash
cast call --rpc-url http://127.0.0.1:8545 \
  <CONTRACT_ADDR> "balanceOf(address)(uint256)" \
  0x000000000000000000000000000000000000dead
```

Expected: `100`

**Step 7: Mint again and verify accumulation**

```bash
cast send --rpc-url http://127.0.0.1:8545 \
  --private-key 0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80 \
  <CONTRACT_ADDR> "mint(address,uint256)" \
  0x000000000000000000000000000000000000dead 50

cast call --rpc-url http://127.0.0.1:8545 \
  <CONTRACT_ADDR> "totalSupply()(uint256)"
# Expected: 150

cast call --rpc-url http://127.0.0.1:8545 \
  <CONTRACT_ADDR> "balanceOf(address)(uint256)" \
  0x000000000000000000000000000000000000dead
# Expected: 150
```

**Step 8: Commit (record test results in commit message)**

```bash
jj commit -m "test(evm): end-to-end — deploy to anvil, mint, verify state via cast"
```

---

## Task 10: Update Design Doc with Findings

**Files:**
- Create: `docs/plans/2026-02-24-evm-codegen-findings.md`

Record:
- Final bytecode size (runtime + deploy)
- Number of opcodes used vs planned
- Any issues encountered during assembly/deployment
- Kill criteria results table (same format as previous sprints)
- Observations for future work (verified codegen, burn/transfer, macro integration)

**Step 1: Write findings doc**

Follow the format from previous sprint findings docs (e.g., `2026-02-23-sprint4-findings.md`).

**Step 2: Commit**

```bash
jj commit -m "docs(sprint5): add findings — EVM codegen assessment"
```
