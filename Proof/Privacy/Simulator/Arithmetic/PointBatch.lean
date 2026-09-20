import Proof.Privacy.Simulator.Arithmetic.PointBatchLoop
import Proof.Privacy.Simulator.Arithmetic.PointBatchSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The standalone point batch contains all its instructions before its halt. -/
theorem pointBatch_self (count attempts : Nat) (fits : 58 * count < 2 ^ 256) :
    ContainsPointBatch (pointBatch count attempts fits) count attempts fits id := by
  intro pc inside
  change (pointBatch count attempts fits).code[pc.val] = relocate id ((pointBatch count attempts fits).code[pc.val])
  generalize (pointBatch count attempts fits).code[pc.val] = instruction
  cases instruction <;> rfl

/-- The final point-batch table entry is a halt instruction. -/
theorem pointBatch_halt_code (count attempts : Nat) (fits : 58 * count < 2 ^ 256) :
    (pointBatch count attempts fits).code[58 * count]'(by change 58 * count < 58 * count + 1; omega) = .halt := by
  simp [pointBatch]

/-- The standalone point batch charges its final halt. -/
theorem pointBatch_halt [BN254.FieldCertificate] (count attempts fuel : Nat) (fits : 58 * count < 2 ^ 256) (base : Memory) :
    run (pointBatch count attempts fits) (fuel + 1) ⟨pointBatchBoundary count (Nat.le_refl count), base⟩ =
      PMF.pure (some (⟨pointBatchBoundary count (Nat.le_refl count), base⟩, 1)) := by
  simp [run, step, pointBatch, pointBatchBoundary]

/-- The complete point machine returns its exact memory law and charges its halt. -/
theorem pointBatch_run [BN254.FieldCertificate] (count attempts : Nat) (fits : 58 * count < 2 ^ 256)
    (base : Memory) (countFits : attempts < 2 ^ 256) :
    run (pointBatch count attempts fits) (pointBatchStepBudget attempts * count + 1) ⟨0, base⟩ =
      (pointBatchMemory attempts 0 count base).map fun result =>
        some (⟨pointBatchBoundary count (Nat.le_refl count), result.1⟩, result.2 + 1) := by
  have continued := pointBatchBlock_run (pointBatch count attempts fits) count attempts fits id
    (pointBatch_self count attempts fits) count 0 1 base (by omega) countFits
  simp only [id_eq, Nat.zero_add] at continued
  apply continued.trans
  change (pointBatchMemory attempts 0 count base).bind _ = (pointBatchMemory attempts 0 count base).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨memory, cost⟩
  have bounded := pointBatchMemory_cost attempts 0 count base memory cost supported
  have amount : pointBatchStepBudget attempts * count + 1 - cost =
      (pointBatchStepBudget attempts * count - cost) + 1 := by omega
  rw [amount, pointBatch_halt]
  simp only [PMF.pure_map, Option.map_some, Nat.add_comm]
  rfl

/-- The point machine stores the exact total point-vector source law. -/
theorem pointBatch_source [BN254.FieldCertificate] [BN254.GroupCertificate]
    (count attempts : Nat) (fits : 58 * count < 2 ^ 256) (base : Memory) (countFits : attempts < 2 ^ 256) :
    (run (pointBatch count attempts fits) (pointBatchStepBudget attempts * count + 1) ⟨0, base⟩).map
      (Option.map fun result => result.1.memory.ram) =
      ((Security.SimulatorSampling.point.vector count).total attempts).law.map
        (fun points => some (storeDrawWords (base.registers 10) 0 base.ram (vectorWords pointWords points))) := by
  rw [pointBatch_run count attempts fits base countFits]
  have source := congrArg (PMF.map some) (pointBatchMemory_source attempts 0 count base)
  simpa only [PMF.map_comp, Function.comp_def, Option.map_some, Nat.mul_zero] using source

/-- The point batch pays for all instructions and every table entry. -/
theorem pointBatch_cost (count attempts : Nat) (fits : 58 * count < 2 ^ 256) :
    pointBatchStepBudget attempts * count + 1 + (pointBatch count attempts fits).size + 1 ≤
      (2574 * attempts + 1619) * count + 2 := by
  have product := Nat.mul_le_mul_right attempts
    (show runtimeTrialCost (BitVec.ofNat 256 BN254.scalarFieldModulus) + 2 ≤ 2574 by
      have bounded := runtimeTrialCost_bound (BitVec.ofNat 256 BN254.scalarFieldModulus)
      omega)
  have one : pointBatchStepBudget attempts ≤ 2574 * attempts + 1561 := by
    unfold pointBatchStepBudget pointSamplerFuel
    omega
  have all := Nat.mul_le_mul_right count one
  change pointBatchStepBudget attempts * count + 1 + 58 * count + 1 ≤ _
  nlinarith

end Kriterion.ArgoMAC.ArithmeticSimulator
