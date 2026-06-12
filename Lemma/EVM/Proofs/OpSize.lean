import Lemma.EVM.Op

/-!
# Op.toBytes_length

Each opcode's byte encoding length matches its predicted size.
-/

namespace EVM.Proofs

theorem Op.toBytes_length (o : EVM.Op) : o.toBytes.length = o.size := by
  cases o <;> simp [EVM.Op.toBytes, EVM.Op.size]

end EVM.Proofs
