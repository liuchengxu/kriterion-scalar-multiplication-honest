import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The standalone online machine contains its complete sampler body. -/
theorem onlineSampling_self (attempts : Nat) : ContainsOnlineSampling (onlineSampling attempts) attempts id := by
  intro pc inside
  change (onlineSampling attempts).code[pc.val] = relocate id ((onlineSampling attempts).code[pc.val])
  generalize (onlineSampling attempts).code[pc.val] = instruction
  cases instruction <;> rfl

/-- A halt instruction ends a machine run in one charged step. -/
private theorem halt_at [BN254.FieldCertificate] (machine : Machine) (pc : Fin (machine.size + 1))
    (code : machine.code[pc.val] = .halt) (fuel : Nat) (base : Memory) :
    run machine (fuel + 1) ⟨pc, base⟩ = PMF.pure (some (⟨pc, base⟩, 1)) := by
  simp [run, step, code]

/-- The online machine charges its final halt. -/
theorem onlineSampling_halt [BN254.FieldCertificate] (attempts fuel : Nat) (base : Memory) :
    run (onlineSampling attempts) (fuel + 1) ⟨(8771 : Fin 8772), base⟩ = PMF.pure (some (⟨(8771 : Fin 8772), base⟩, 1)) := by
  apply halt_at
  change (onlineCode attempts)[8771] = .halt
  rw [onlineCode, Vector.getElem_ofFn]
  simp

/-- The online machine returns its exact memory and charges its halt. -/
theorem onlineSampling_run [BN254.FieldCertificate] (attempts : Nat) (base : Memory)
    (countFits : attempts < 2 ^ 256) :
    run (onlineSampling attempts) (onlineSamplingBudget attempts + 1) ⟨(0 : Fin 8772), base⟩ =
      (onlineSamplingMemory attempts base).map fun result => some (⟨(8771 : Fin 8772), result.1⟩, result.2 + 1) := by
  have continued := onlineSamplingBlock_run (onlineSampling attempts) attempts id (onlineSampling_self attempts)
    1 base countFits
  simp only [id_eq] at continued
  apply continued.trans
  change (onlineSamplingMemory attempts base).bind _ = (onlineSamplingMemory attempts base).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨memory, cost⟩
  have bounded := onlineSamplingMemory_cost attempts base memory cost supported
  have amount : onlineSamplingBudget attempts + 1 - cost = (onlineSamplingBudget attempts - cost) + 1 := by omega
  rw [amount]
  dsimp only
  rw [onlineSampling_halt]
  simp only [PMF.pure_map, Option.map_some, Nat.add_comm]
  rfl

/-- The online machine stores the exact total law of 92 scales and 91 points. -/
theorem onlineSampling_source [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (base : Memory) (countFits : attempts < 2 ^ 256) :
    (run (onlineSampling attempts) (onlineSamplingBudget attempts + 1) ⟨(0 : Fin 8772), base⟩).map
      (Option.map fun result => result.1.memory.ram) =
      (Security.SimulatorSampling.online.total attempts).law.map
        (fun sample => some (storeDrawWords (base.registers 10) 0 base.ram (onlineWords sample))) := by
  rw [onlineSampling_run attempts base countFits]
  have source := congrArg (PMF.map some) (onlineSamplingMemory_source attempts base)
  simpa only [PMF.map_comp, Function.comp_def, Option.map_some] using source

/-- The online budget includes both phases and every instruction-table entry. -/
theorem onlineSampling_cost (attempts : Nat) :
    onlineSamplingBudget attempts + 1 + (onlineSampling attempts).size + 1 ≤
      183 * (2574 * attempts) + 151935 := by
  have points := pointBatch_cost 90 attempts (by decide)
  dsimp only [pointBatch] at points
  rw [show (onlineSampling attempts).size = 8771 from rfl]
  unfold onlineSamplingBudget batchStepBudget
  omega

/-- The default online sampler pays at most 120738687 fixed arithmetic units. -/
theorem onlineSampling_256_cost :
    onlineSamplingBudget 256 + 1 + (onlineSampling 256).size + 1 ≤ 120738687 :=
  onlineSampling_cost 256

end Kriterion.ArgoMAC.ArithmeticSimulator
