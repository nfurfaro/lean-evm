import Lemma.EVM.Codegen.Contract

namespace EVM

/-- Convert a byte to its 2-character hex representation. -/
def byteToHex (b : UInt8) : String :=
  let hi := b >>> 4
  let lo := b &&& 0x0f
  let hexChar (n : UInt8) : Char :=
    if n < 10 then Char.ofNat (48 + n.toNat)   -- '0'..'9'
    else Char.ofNat (87 + n.toNat)              -- 'a'..'f'
  String.ofList [hexChar hi, hexChar lo]

/-- Convert a ByteArray to a hex string (no 0x prefix). -/
def bytesToHex (bs : ByteArray) : String :=
  bs.foldl (fun acc b => acc ++ byteToHex b) ""

/-- The full deployment bytecode as a hex string. -/
def deployHex : Option String :=
  Codegen.deployCode.map (fun bs => "0x" ++ bytesToHex bs)

end EVM

/-- Print the deployable bytecode. -/
def printDeployHex : IO Unit :=
  match EVM.deployHex with
  | some hex => IO.println hex
  | none     => IO.println "ERROR: label resolution failed"

-- Entry point: `lake env lean --run Lemma/EVM/Hex.lean`.
def main : IO Unit := printDeployHex
