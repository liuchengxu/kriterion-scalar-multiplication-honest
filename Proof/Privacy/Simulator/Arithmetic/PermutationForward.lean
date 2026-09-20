import Construction.Simulator.PermutationForward
import Proof.Privacy.Simulator.Arithmetic.KnownQueryBlock
import Proof.Privacy.Simulator.Arithmetic.FreshQueryComplete

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The forward handler contains the complete known-query path. -/
theorem permutationForward_known (attempts : Nat) :
    ContainsKnownQuery (permutationForward attempts) permutationKnownLabels := by
  intro pc valid
  have bound : pc.val < 38 := by
    have small := pc.isLt
    have different : pc.val ≠ 38 := by intro eq; apply valid; exact Fin.ext eq
    omega
  simp [permutationForward, permutationKnownLabels, bound]
  rfl

/-- The forward handler contains the complete fresh-query path. -/
theorem permutationForward_fresh (attempts : Nat) :
    ContainsFreshQuery (permutationForward attempts) attempts permutationFreshLabels := by
  intro pc valid
  have bound : pc.val < 114 := by
    have small := pc.isLt
    have different : pc.val ≠ 114 := by intro eq; apply valid; exact Fin.ext eq
    omega
  simp [permutationForward, permutationFreshLabels, show ¬ pc.val + 39 < 38 by omega,
    show pc.val + 39 < 153 by omega]
  rfl

/-- The known-query path preserves the persistent metadata registers. -/
theorem knownQueryScan_metadata (inputCount outputCount : Nat) (memory : Memory)
    (register : Register) (low : register.val < 6) :
    (knownQueryScan inputCount outputCount memory).1.registers register = memory.registers register := by
  unfold knownQueryScan knownQueryBranch
  dsimp only
  split
  · exact inverseProbe_metadata inputCount memory register low
  · rw [swapScan_caller _ _ register (by omega)]
    have notSix : register ≠ 6 := by intro eq; subst register; norm_num at low
    have notNine : register ≠ 9 := by intro eq; subst register; norm_num at low
    have notTen : register ≠ 10 := by intro eq; subst register; norm_num at low
    simp only [swapInitial, knownQueryInitial,
      Function.update_of_ne (show register ≠ 14 by intro eq; subst register; norm_num at low),
      Function.update_of_ne notTen, Function.update_of_ne notNine, Function.update_of_ne notSix]
    exact inverseProbe_metadata inputCount memory register low

/-- The known-query path preserves RAM and all bit stacks. -/
theorem knownQueryScan_data (inputCount outputCount : Nat) (memory : Memory) :
    (knownQueryScan inputCount outputCount memory).1.ram = memory.ram ∧
      (knownQueryScan inputCount outputCount memory).1.bits = memory.bits := by
  have inverseBits : (inverseProbeFinal (reverseSwapScan inputCount
      (reverseSwapInitial (inverseProbeInitial memory))).1).bits = memory.bits := by
    change (reverseSwapScan inputCount (reverseSwapInitial (inverseProbeInitial memory))).1.bits = _
    rw [(reverseSwapScan_data _ _).1]
    rfl
  unfold knownQueryScan knownQueryBranch
  dsimp only
  split
  · exact ⟨inverseProbe_ram inputCount memory, inverseBits⟩
  · rw [(swapScan_data _ _).1, (swapScan_data _ _).2]
    exact ⟨inverseProbe_ram inputCount memory, inverseBits⟩

/-- The source retains known answers and applies the full fresh-query distribution otherwise. -/
noncomputable def permutationForwardSamples (attempts inputCount outputCount : Nat)
    (memory : Memory) : PMF (Memory × Nat) :=
  let known := knownQueryScan inputCount outputCount memory
  if known.1.registers 7 = 0#256 then
    (freshChoiceSamples attempts known.1).map fun result =>
      let tail := freshQueryTail outputCount (freshChoiceFinal result.1)
      (tail.1, tail.2 + (freshChoiceTailCost result.1 - 1) + (result.2 + 1) + 15 + known.2)
  else PMF.pure (known.1, known.2 + 1)

/-- The branch selects the fresh path or the final return in one instruction. -/
theorem permutationForward_branch [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (permutationForward attempts) (fuel + 1) ⟨38, memory⟩ =
      (run (permutationForward attempts) fuel
        ⟨if memory.registers 7 = 0#256 then 39 else 153, memory⟩).map
        (Option.map fun result => (result.1, result.2 + 1)) := by
  have code : (permutationForward attempts).code[38]'(by change 38 < 154; decide) =
      .branch 7 39 153 := by simp [permutationForward]; rfl
  rw [run]
  simp only [step, show (38 : Fin ((permutationForward attempts).size + 1)).val = 38 from rfl,
    code, PMF.pure_bind]
  rfl

/-- The final return halts in one instruction. -/
theorem permutationForward_halt [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (permutationForward attempts) (fuel + 1) ⟨153, memory⟩ =
      PMF.pure (some (⟨153, memory⟩, 1)) := by
  have code : (permutationForward attempts).code[153]'(by change 153 < 154; decide) =
      .halt := by simp [permutationForward]
  simp only [run, step, show (153 : Fin ((permutationForward attempts).size + 1)).val = 153 from rfl,
    code, PMF.pure_bind]

/-- The forward handler implements the complete known-or-fresh source and its actual charge. -/
theorem permutationForward_run [BN254.FieldCertificate] (attempts inputCount outputCount : Nat)
    (memory : Memory) (countFits : attempts < 2 ^ 256)
    (inputFits : inputCount < 2 ^ 256) (outputFits : outputCount < 2 ^ 256)
    (inputCounter : memory.registers 2 = BitVec.ofNat 256 inputCount)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 outputCount) :
    run (permutationForward attempts)
      ((knownQueryScan inputCount outputCount memory).2 +
        (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
        11 * outputCount + 76) ⟨0, memory⟩ =
      (permutationForwardSamples attempts inputCount outputCount memory).map
        (fun result => some (⟨153, result.1⟩, result.2)) := by
  let known := knownQueryScan inputCount outputCount memory
  let budget := (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
    11 * outputCount + 76
  have positive : 1 ≤ known.2 := by
    dsimp [known, knownQueryScan]
    omega
  rw [show (knownQueryScan inputCount outputCount memory).2 +
    (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
    11 * outputCount + 76 = (known.2 - 1) + (budget + 1) by change known.2 + _ + _ + _ = _; dsimp [budget]; omega]
  have continued := knownQueryBlock_continue (permutationForward attempts) permutationKnownLabels
    (permutationForward_known attempts) inputCount outputCount memory inputFits outputFits
    inputCounter outputCounter (budget + 1)
  change run (permutationForward attempts) _ ⟨0, memory⟩ = _ at continued
  rw [continued]
  change (run (permutationForward attempts) (budget + 1) ⟨38, known.1⟩).map _ = _
  rw [permutationForward_branch]
  by_cases fresh : known.1.registers 7 = 0#256
  · simp only [if_pos fresh]
    have full := freshQueryBlock_complete (permutationForward attempts) attempts outputCount
      permutationFreshLabels (permutationForward_fresh attempts)
      (by simp [permutationForward, permutationFreshLabels])
      known.1 countFits outputFits
      (by rw [knownQueryScan_metadata _ _ _ 4 (by decide)]; exact outputCounter)
    have boundEq : known.1.registers 5 - known.1.registers 0 =
        memory.registers 5 - memory.registers 0 := by
      rw [knownQueryScan_metadata _ _ _ 5 (by decide), knownQueryScan_metadata _ _ _ 0 (by decide)]
    rw [boundEq] at full
    change run (permutationForward attempts) budget ⟨39, known.1⟩ = _ at full
    rw [full]
    change _ = ((if known.1.registers 7 = 0#256 then
      (freshChoiceSamples attempts known.1).map (fun result =>
        ((freshQueryTail outputCount (freshChoiceFinal result.1)).1,
          (freshQueryTail outputCount (freshChoiceFinal result.1)).2 +
          (freshChoiceTailCost result.1 - 1) + (result.2 + 1) + 15 + known.2))
      else PMF.pure (known.1, known.2 + 1)).map _)
    simp only [if_pos fresh, PMF.map_comp, Function.comp_def, Option.map_some]
    congr 1
    funext result
    congr 2
    change _ + 1 + (known.2 - 1) = _ + known.2
    omega
  · simp only [if_neg fresh]
    have fuelPositive : 1 ≤ budget := by dsimp [budget]; omega
    rw [show budget = (budget - 1) + 1 by omega, permutationForward_halt, PMF.pure_map, PMF.pure_map]
    change _ = ((if known.1.registers 7 = 0#256 then _ else PMF.pure (known.1, known.2 + 1)).map _)
    simp only [if_neg fresh, PMF.pure_map, Option.map_some]
    congr 3
    change 1 + 1 + (known.2 - 1) = known.2 + 1
    omega

/-- The total forward-handler budget is linear in stored pairs and sampler attempts. -/
theorem permutationForward_budget (attempts inputCount outputCount : Nat) (memory : Memory) :
    (permutationForward attempts).size + 1 +
      ((knownQueryScan inputCount outputCount memory).2 +
        (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
        11 * outputCount + 76) ≤
      2574 * attempts + 11 * inputCount + 22 * outputCount + 247 := by
  have knownBound := knownQuery_budget inputCount outputCount memory
  have trialBound := runtimeTrialCost_bound (memory.registers 5 - memory.registers 0)
  change 153 + 1 + _ ≤ _
  have multiplied : (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts ≤
      2574 * attempts := Nat.mul_le_mul_right attempts (by omega)
  change 38 + 1 + _ ≤ _ at knownBound
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
