import Lemma.EVM.Asm
import Lemma.EVM.Codegen.Getters

/-!
# Assembly Lemma: totalSupplyCode

Proves that `assemble totalSupplyCode` produces the exact byte sequence
used in the execution correctness proof.
-/

namespace EVM

theorem totalSupply_asm :
    assemble Codegen.totalSupplyCode =
    some [0x60, 0x00, 0x54, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3] := by
  native_decide

end EVM
