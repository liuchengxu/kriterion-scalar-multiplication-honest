import Construction.Simulator.PointNegation
import Proof.Privacy.Simulator.Arithmetic.HomogeneousPoint

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The negation return changes only the zero scratch word and the affine y coordinate. -/
def pointNegationMemory [BN254.FieldCertificate] (base : Memory) : BN254.Point → Memory
  | .zero => {base with registers := Function.update base.registers 0 0}
  | .some _ y _ => {base with registers := Function.update (Function.update base.registers 0 0) 4 (BitVec.ofNat 256 (-y).val)}

/-- The identity path avoids the unnecessary field subtraction. -/
def pointNegationCost [BN254.FieldCertificate] : BN254.Point → Nat
  | .zero => 2
  | .some _ _ _ => 3

/-- A host contains every point-negation instruction before its return. -/
def ContainsPointNegation (host : Machine) (labels : Fin 4 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 4, pc.val < 3 → host.code[(labels pc).val] =
    relocate labels (pointNegation.code[pc.val]'(by exact pc.isLt))

/-- The fixed field-subtract instruction computes the canonical negative field word. -/
theorem fieldNeg_word (value : BN254.BaseField) :
    Arithmetic.fieldSub.eval 0#256 (BitVec.ofNat 256 value.val) = BitVec.ofNat 256 (-value).val := by
  simp only [Arithmetic.eval, BitVec.toNat_zero, Nat.cast_zero, baseField_word_value, ZMod.natCast_zmod_val, zero_sub]

/-- The host negates the canonical point and charges its exact path length. -/
theorem pointNegationBlock_run [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 4 → Fin (host.size + 1)) (present : ContainsPointNegation host labels)
    (fuel : Nat) (base : Memory) (point : BN254.Point) (encoded : PointAccumulatorEncoding base point) :
    run host (fuel + pointNegationCost point) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels 3, pointNegationMemory base point⟩).map
        (Option.map fun result => (result.1, result.2 + pointNegationCost point)) := by
  cases point <;>
    simp only [PointAccumulatorEncoding, writePoint, scalarAccumulator, Function.update_self,
      Function.update_of_ne (by decide : (2 : Register) ≠ 3),
      Function.update_of_ne (by decide : (2 : Register) ≠ 4),
      Function.update_of_ne (by decide : (3 : Register) ≠ 4)] at encoded <;>
    simp [run, step, present 0 (by decide), present 1 (by decide), present 2 (by decide), pointNegation,
      relocate, encoded.1, encoded.2.2, fieldNeg_word, pointNegationMemory, pointNegationCost,
      PMF.map_comp, Option.map_map, Function.comp_def, Function.update_comm, Nat.add_assoc]

/-- The point-negation return has the canonical encoding of the group negative. -/
theorem pointNegationMemory_encoding [BN254.FieldCertificate] (base : Memory) (point : BN254.Point)
    (encoded : PointAccumulatorEncoding base point) :
    PointAccumulatorEncoding (pointNegationMemory base point) (-point) := by
  change PointAccumulatorEncoding (pointNegationMemory base point) (WeierstrassCurve.Affine.Point.neg point)
  cases point <;>
    simp_all [PointAccumulatorEncoding, pointNegationMemory, writePoint, scalarAccumulator,
      WeierstrassCurve.Affine.Point.neg_def, WeierstrassCurve.Affine.Point.neg, WeierstrassCurve.Affine.negY, BN254.curve,
      WeierstrassCurve.toAffine]

/-- Point negation preserves every register except zero and four. -/
theorem pointNegationMemory_register [BN254.FieldCertificate] (base : Memory) (point : BN254.Point)
    (register : Register) (notZero : register ≠ 0) (notY : register ≠ 4) :
    (pointNegationMemory base point).registers register = base.registers register := by
  cases point <;> simp [pointNegationMemory, notZero, notY]

end Kriterion.ArgoMAC.ArithmeticSimulator
