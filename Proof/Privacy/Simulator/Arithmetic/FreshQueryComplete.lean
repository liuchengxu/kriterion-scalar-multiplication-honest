import Proof.Privacy.Simulator.Arithmetic.FreshQueryBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A host halt closes the fresh query with the exact source state and charge. -/
theorem freshQueryBlock_complete [BN254.FieldCertificate] (host : Machine) (attempts outputCount : Nat)
    (labels : Fin 115 → Fin (host.size + 1)) (present : ContainsFreshQuery host attempts labels)
    (halted : host.code[(labels 114).val] = .halt)
    (memory : Memory) (countFits : attempts < 2 ^ 256) (outputFits : outputCount < 2 ^ 256)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 outputCount) :
    run host ((runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
      11 * outputCount + 76) ⟨labels 0, memory⟩ =
      (freshChoiceSamples attempts memory).map fun result =>
        let tail := freshQueryTail outputCount (freshChoiceFinal result.1)
        some (⟨labels 114, tail.1⟩,
          tail.2 + (freshChoiceTailCost result.1 - 1) + (result.2 + 1) + 15) := by
  let bound := memory.registers 5 - memory.registers 0
  let reserve := (runtimeTrialCost bound + 2) * attempts + 3 + (20 + (11 * outputCount + 37 + 1))
  have continued := freshQueryBlock_run host attempts outputCount 1 labels present memory countFits
    outputFits outputCounter
  dsimp only at continued
  rw [show (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
    11 * outputCount + 76 = 15 + reserve by dsimp [reserve, bound]; omega]
  rw [continued]
  change (freshChoiceSamples attempts memory).bind _ = (freshChoiceSamples attempts memory).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨sampled, cost⟩
  have sampleBound := runtimeSamplerMemory_cost _ _ _ sampled cost supported
  have choiceBound := freshChoiceTailCost_bounds sampled
  have tailBound := freshQueryTail_cost outputCount (freshChoiceFinal sampled)
  have tailPositive : 1 ≤ (freshQueryTail outputCount (freshChoiceFinal sampled)).2 := by
    unfold freshQueryTail
    split <;> simp
  have remaining : 1 ≤ reserve - (cost + 1) - (freshChoiceTailCost sampled - 1) -
      ((freshQueryTail outputCount (freshChoiceFinal sampled)).2 - 1) := by
    dsimp [reserve, bound]
    omega
  change (run host (reserve - (cost + 1) - (freshChoiceTailCost sampled - 1) -
    ((freshQueryTail outputCount (freshChoiceFinal sampled)).2 - 1))
    ⟨labels 114, (freshQueryTail outputCount (freshChoiceFinal sampled)).1⟩).map _ = _
  rw [show reserve - (cost + 1) - (freshChoiceTailCost sampled - 1) -
    ((freshQueryTail outputCount (freshChoiceFinal sampled)).2 - 1) =
      (reserve - (cost + 1) - (freshChoiceTailCost sampled - 1) -
        ((freshQueryTail outputCount (freshChoiceFinal sampled)).2 - 1) - 1) + 1 by omega]
  simp only [run, step, halted, PMF.pure_bind, PMF.pure_map, Option.map_some]
  congr 3
  change 1 + ((freshQueryTail outputCount (freshChoiceFinal sampled)).2 - 1) +
    (freshChoiceTailCost sampled - 1) + (cost + 1) + 15 =
    (freshQueryTail outputCount (freshChoiceFinal sampled)).2 +
      (freshChoiceTailCost sampled - 1) + (cost + 1) + 15
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
