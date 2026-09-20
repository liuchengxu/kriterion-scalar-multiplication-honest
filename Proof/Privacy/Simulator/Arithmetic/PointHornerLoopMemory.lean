import Proof.Privacy.Simulator.Arithmetic.PointHornerBlock
import Construction.ArgoMAC.Algebra

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- One Horner entry preserves caller data and returns the exact group value. -/
theorem hornerStepMemory_spec [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (index : Nat) (current next : BN254.Point)
    (input : readPoint base.registers scalarMultiple = some current) :
    readPoint (hornerStepMemory base index current next).registers scalarMultiple = some (next + radix • current) ∧
    (hornerStepMemory base index current next).bits = base.bits ∧
    (hornerStepMemory base index current next).ram = base.ram ∧
    ∀ register : Register, 9 ≤ register.val →
      (hornerStepMemory base index current next).registers register = base.registers register := by
  have spec := hornerScaled_spec base current input
  refine ⟨?_, spec.2.1, spec.2.2.1, ?_⟩
  · exact (hornerTailMemory_point _ _ _ _).trans (congrArg some (add_comm _ _))
  · intro register caller
    exact (hornerTailMemory_caller _ _ _ _ register caller).trans (spec.2.2.2 register caller)

/-- The initial memory fixes zero, one, and the zero point. -/
def hornerInitial (base : Memory) : Memory :=
  {base with registers := Function.update (Function.update (Function.update (Function.update
    (Function.update base.registers 9 0) 12 1) 5 0) 6 0) 7 0}

/-- The initial point is the group identity. -/
theorem hornerInitial_point [BN254.FieldCertificate] (base : Memory) :
    readPoint (hornerInitial base).registers scalarMultiple = some (0 : BN254.Point) := by
  simp [hornerInitial, readPoint, scalarMultiple]

/-- This memory records each reverse-order point update. -/
def hornerPrefixMemory [BN254.FieldCertificate] [BN254.GroupCertificate]
    (points : List BN254.Point) : Nat → Memory → Memory
  | 0, base => base
  | n + 1, base => hornerStepMemory (hornerPrefixMemory points n base) (points.length - 1 - n)
      (pointHorner radix (points.drop (points.length - n))) ((points[points.length - 1 - n]?).getD 0)

/-- One reverse-order point update extends the exact source suffix. -/
theorem pointHorner_suffix_step [BN254.FieldCertificate] [BN254.GroupCertificate]
    (points : List BN254.Point) (n : Nat) (inside : n < points.length) :
    (points[points.length - 1 - n]?).getD 0 + radix • pointHorner radix (points.drop (points.length - n)) =
      pointHorner radix (points.drop (points.length - (n + 1))) := by
  have atIndex : points.length - 1 - n < points.length := by omega
  have indexEq : points.length - (n + 1) = points.length - 1 - n := by omega
  have nextEq : points.length - 1 - n + 1 = points.length - n := by omega
  rw [indexEq, List.drop_eq_getElem_cons atIndex, pointHorner, nextEq]
  simp only [List.getElem?_eq_getElem atIndex, Option.getD_some]

/-- Every Horner prefix has the exact source suffix and preserves caller data. -/
theorem hornerPrefixMemory_spec [BN254.FieldCertificate] [BN254.GroupCertificate]
    (points : List BN254.Point) (n : Nat) (inside : n ≤ points.length) (base : Memory)
    (input : readPoint base.registers scalarMultiple = some (0 : BN254.Point)) :
    readPoint (hornerPrefixMemory points n base).registers scalarMultiple =
      some (pointHorner radix (points.drop (points.length - n))) ∧
    (hornerPrefixMemory points n base).bits = base.bits ∧
    (hornerPrefixMemory points n base).ram = base.ram ∧
    ∀ register : Register, 9 ≤ register.val →
      (hornerPrefixMemory points n base).registers register = base.registers register := by
  induction n with
  | zero => simpa [hornerPrefixMemory, pointHorner] using input
  | succ n ih =>
      have prior := ih (by omega)
      have current := hornerStepMemory_spec (hornerPrefixMemory points n base) (points.length - 1 - n)
        (pointHorner radix (points.drop (points.length - n))) ((points[points.length - 1 - n]?).getD 0) prior.1
      rw [pointHorner_suffix_step points n (by omega)] at current
      exact ⟨current.1, current.2.1.trans prior.2.1, current.2.2.1.trans prior.2.2.1,
        fun register caller => (current.2.2.2 register caller).trans (prior.2.2.2 register caller)⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
