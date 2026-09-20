import Proof.Privacy.Simulator.Arithmetic.PermutationForwardBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The handler reserves a fixed bound for all instructions before its return. -/
def permutationForwardCost (attempts inputCount outputCount : Nat) (memory : Memory) : Nat :=
  (knownQueryScan inputCount outputCount memory).2 +
    (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
    11 * outputCount + 75

/-- The host return law uses the same complete source distribution as the closed handler. -/
theorem permutationForwardBlock_continue [BN254.FieldCertificate] (host : Machine)
    (attempts inputCount outputCount fuel : Nat)
    (labels : Fin 154 → Fin (host.size + 1)) (present : ContainsPermutationForward host attempts labels)
    (memory : Memory) (countFits : attempts < 2 ^ 256)
    (inputFits : inputCount < 2 ^ 256) (outputFits : outputCount < 2 ^ 256)
    (inputCounter : memory.registers 2 = BitVec.ofNat 256 inputCount)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 outputCount) :
    let reserve := permutationForwardCost attempts inputCount outputCount memory + fuel
    run host reserve ⟨labels 0, memory⟩ =
      (permutationForwardSamples attempts inputCount outputCount memory).bind fun result =>
        (run host (reserve - (result.2 - 1)) ⟨labels 153, result.1⟩).map
          (Option.map fun final => (final.1, final.2 + (result.2 - 1))) := by
  dsimp only
  let known := knownQueryScan inputCount outputCount memory
  let reserve := (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
    3 + (20 + (11 * outputCount + 37 + fuel))
  have positive : 1 ≤ known.2 := by dsimp [known, knownQueryScan]; omega
  have reordered : permutationForwardCost attempts inputCount outputCount memory + fuel =
      known.2 + 15 + reserve := by dsimp [permutationForwardCost, known, reserve]; omega
  rw [reordered]
  have source := permutationForwardBlock_run host attempts inputCount outputCount fuel labels present
    memory countFits inputFits outputFits inputCounter outputCounter
  dsimp only at source
  change run host (known.2 + 15 + reserve) ⟨labels 0, memory⟩ = _ at source
  rw [source]
  unfold permutationForwardSamples
  change (if known.1.registers 7 = 0#256 then _ else _) =
    ((if known.1.registers 7 = 0#256 then _ else _) : PMF (Memory × Nat)).bind _
  by_cases fresh : known.1.registers 7 = 0#256
  · simp only [if_pos fresh, PMF.bind_map, Function.comp_def]
    change (freshChoiceSamples attempts known.1).bind _ = (freshChoiceSamples attempts known.1).bind _
    congr 1
    funext result
    rcases result with ⟨sampled, cost⟩
    let tail := freshQueryTail outputCount (freshChoiceFinal sampled)
    have tailPositive : 1 ≤ tail.2 := by dsimp [tail, freshQueryTail]; split <;> simp
    have charge : (tail.2 + (freshChoiceTailCost sampled - 1) + (cost + 1) + 15 + known.2) - 1 =
        (tail.2 - 1) + (freshChoiceTailCost sampled - 1) + (cost + 1) + 15 + known.2 := by omega
    change (run host (reserve - (cost + 1) - (freshChoiceTailCost sampled - 1) - (tail.2 - 1))
      ⟨labels 153, tail.1⟩).map _ =
      (run host ((known.2 + 15 + reserve) -
        ((tail.2 + (freshChoiceTailCost sampled - 1) + (cost + 1) + 15 + known.2) - 1))
        ⟨labels 153, tail.1⟩).map _
    rw [charge]
    have remaining : known.2 + 15 + reserve -
        ((tail.2 - 1) + (freshChoiceTailCost sampled - 1) + (cost + 1) + 15 + known.2) =
        reserve - (cost + 1) - (freshChoiceTailCost sampled - 1) - (tail.2 - 1) := by omega
    rw [remaining]
    simp [Nat.add_assoc]
    rfl
  · simp only [if_neg fresh, PMF.pure_bind]
    change (run host (15 + reserve) ⟨labels 153, known.1⟩).map _ =
      (run host (known.2 + 15 + reserve - ((known.2 + 1) - 1)) ⟨labels 153, known.1⟩).map _
    simp [Nat.add_assoc]

/-- Every source outcome fits the reserved closed-handler execution budget. -/
theorem permutationForwardSamples_cost [BN254.FieldCertificate]
    (attempts inputCount outputCount : Nat) (memory final : Memory) (cost : Nat)
    (countFits : attempts < 2 ^ 256) (inputFits : inputCount < 2 ^ 256) (outputFits : outputCount < 2 ^ 256)
    (inputCounter : memory.registers 2 = BitVec.ofNat 256 inputCount)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 outputCount)
    (supported : (final, cost) ∈ (permutationForwardSamples attempts inputCount outputCount memory).support) :
    cost ≤ permutationForwardCost attempts inputCount outputCount memory + 1 := by
  have member : some ((⟨153, final⟩ : Configuration ((permutationForward attempts).size + 1)), cost) ∈
      (run (permutationForward attempts)
        ((knownQueryScan inputCount outputCount memory).2 +
          (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
          11 * outputCount + 76) ⟨0, memory⟩).support := by
    rw [permutationForward_run attempts inputCount outputCount memory countFits inputFits outputFits
      inputCounter outputCounter]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(final, cost), supported, rfl⟩
  have bound := run_cost _ _ _ _ _ member
  dsimp [permutationForwardCost]
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
