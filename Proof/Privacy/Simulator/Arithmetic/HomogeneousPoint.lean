import Construction.Simulator.HomogeneousPoint
import Proof.Privacy.Simulator.Arithmetic.PointBatchMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- This predicate fixes the canonical point words in the accumulator registers. -/
def PointAccumulatorEncoding [BN254.FieldCertificate] (base : Memory) (point : BN254.Point) : Prop :=
  base.registers 2 = (writePoint (fun _ => 0) scalarAccumulator point) 2 ∧
  base.registers 3 = (writePoint (fun _ => 0) scalarAccumulator point) 3 ∧
  base.registers 4 = (writePoint (fun _ => 0) scalarAccumulator point) 4

/-- The homogeneous return memory stores the exact typed coordinate values. -/
def homogeneousMemory [BN254.FieldCertificate] (base : Memory) (point : BN254.Point) (scale : BN254.NonZeroBase) : Memory :=
  let value := Security.homogeneousOfPoint point scale
  {base with registers := Function.update (Function.update (Function.update (Function.update base.registers 8 0)
    5 (BitVec.ofNat 256 value.x.val)) 6 (BitVec.ofNat 256 value.y.val)) 7 (BitVec.ofNat 256 value.z.val)}

/-- A host contains each homogeneous conversion instruction before the return. -/
def ContainsHomogeneousPoint (host : Machine) (labels : Fin 9 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 9, pc.val < 8 → host.code[(labels pc).val] =
    relocate labels (homogeneousPoint.code[pc.val]'(by exact pc.isLt))

/-- The fixed field-multiply instruction preserves canonical field values. -/
theorem fieldMul_words (left right : BN254.BaseField) :
    Arithmetic.fieldMul.eval (BitVec.ofNat 256 left.val) (BitVec.ofNat 256 right.val) =
      BitVec.ofNat 256 (left * right).val := by
  simp only [Arithmetic.eval, baseField_word_value, ZMod.natCast_zmod_val]

private theorem wordAdd_eval (left right : Word) : Arithmetic.add.eval left right = left + right := rfl

/-- The host computes the exact homogeneous coordinates in five charged instructions. -/
theorem homogeneousPointBlock_run [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 9 → Fin (host.size + 1)) (present : ContainsHomogeneousPoint host labels)
    (fuel : Nat) (base : Memory) (point : BN254.Point) (scale : BN254.NonZeroBase)
    (encoded : PointAccumulatorEncoding base point)
    (scaled : base.registers 0 = BitVec.ofNat 256 scale.value.val) :
    run host (fuel + 5) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels 8, homogeneousMemory base point scale⟩).map
        (Option.map fun result => (result.1, result.2 + 5)) := by
  cases point with
  | zero =>
      simp only [PointAccumulatorEncoding, writePoint, scalarAccumulator, Function.update_self,
        Function.update_of_ne (by decide : (2 : Register) ≠ 3),
        Function.update_of_ne (by decide : (2 : Register) ≠ 4),
        Function.update_of_ne (by decide : (3 : Register) ≠ 4)] at encoded
      simp [run, step, present 0 (by decide), present 1 (by decide), present 2 (by decide),
        present 3 (by decide), present 4 (by decide), homogeneousPoint, relocate,
        wordAdd_eval, encoded.1, scaled, homogeneousMemory, Security.homogeneousOfPoint,
        PMF.map_comp, Option.map_map, Function.comp_def, Function.update_comm, Nat.add_assoc]
  | some x y valid =>
      simp only [PointAccumulatorEncoding, writePoint, scalarAccumulator, Function.update_self,
        Function.update_of_ne (by decide : (2 : Register) ≠ 3),
        Function.update_of_ne (by decide : (2 : Register) ≠ 4),
        Function.update_of_ne (by decide : (3 : Register) ≠ 4)] at encoded
      simp [run, step, present 0 (by decide), present 1 (by decide), present 5 (by decide),
        present 6 (by decide), present 7 (by decide), homogeneousPoint, relocate,
        encoded.1, encoded.2.1, encoded.2.2, scaled, fieldMul_words, wordAdd_eval, homogeneousMemory, Security.homogeneousOfPoint,
        PMF.map_comp, Option.map_map, Function.comp_def, Function.update_comm, Nat.add_assoc]

/-- Homogeneous conversion preserves every register outside five through eight. -/
theorem homogeneousMemory_register [BN254.FieldCertificate] (base : Memory) (point : BN254.Point) (scale : BN254.NonZeroBase)
    (register : Register) (outside : register.val < 5 ∨ 9 ≤ register.val) :
    (homogeneousMemory base point scale).registers register = base.registers register := by
  have different (target : Register) (lower : 5 ≤ target.val) (upper : target.val < 9) : register ≠ target := by
    intro equal
    have values := congrArg Fin.val equal
    omega
  simp only [homogeneousMemory, Function.update_of_ne (different 5 (by decide) (by decide)),
    Function.update_of_ne (different 6 (by decide) (by decide)), Function.update_of_ne (different 7 (by decide) (by decide)),
    Function.update_of_ne (different 8 (by decide) (by decide))]

end Kriterion.ArgoMAC.ArithmeticSimulator
