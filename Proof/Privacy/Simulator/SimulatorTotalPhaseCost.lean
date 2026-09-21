import Proof.Privacy.Simulator.SimulatorExternalBits

namespace Kriterion.ArgoMAC.Security
open Cryptography OperationalOracle BoundedIntegerSampling
namespace SimulatorMachine.PhaseCost

/-- The total phase bound starts from the actual empty oracle state.
Both resource fields refer to the same external and private executions. -/
theorem total_all_phase_bound {Before Chosen Encoded Result Seed : Type}
    {q0 q1 privateBudget q2 : Nat}
    (attempts : Nat) (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (seed : Seed)
    (first : OracleProgram Garbling.oracleSpec Before q0)
    (second : Before → OracleProgram Garbling.oracleSpec Chosen q1)
    (privateStage : Chosen → Program combinedSpec Encoded privateBudget)
    (last : Chosen → Encoded → OracleProgram Garbling.oracleSpec Result q2)
    (before : (Before × SparseState) × Nat × Nat)
    (beforeReached : before ∈ (ExternalBits.runTotalWithResources attempts first
      (initial initialMetadata) 0).support)
    (chosen : (Chosen × SparseState) × Nat × Nat)
    (chosenReached : chosen ∈ (ExternalBits.runTotalWithResources attempts
      (second before.1.1) before.1.2 q0).support) :
    let total := q0 + q1 + privateBudget + q2
    let encoded := Cost.executeTotalCost random attempts (privateStage chosen.1.1)
      chosen.1.2 seed (q0 + q1)
    ∀ decided : (Result × SparseState) × Nat × Nat,
      decided ∈ (ExternalBits.runTotalWithResources attempts (last chosen.1.1 encoded.1.1)
        encoded.1.2.1 (q0 + q1 + privateBudget)).support →
      before.2.1 + chosen.2.1 + encoded.2.2.1 + decided.2.1 ≤ total * (10 * total + 16) ∧
      before.2.2 + chosen.2.2 + encoded.2.2.2 + decided.2.2 ≤ total * (257 * attempts) ∧
      Nonempty (Cost.StateBound decided.1.2 total) := by
  let total := q0 + q1 + privateBudget + q2
  let unit := 10 * total + 16
  have empty : Cost.StateBound (initial initialMetadata) 0 :=
    Cost.initialBound initialMetadata 0 (by rfl) (by rfl) (by rfl)
  obtain ⟨firstCost, firstBits, firstState⟩ := ExternalBits.runTotalWithResources_bound attempts first
    (initial initialMetadata) 0 0 empty (Nat.le_refl _) before beforeReached
  obtain ⟨priorBound⟩ := firstState
  have priorBound' : Cost.StateBound before.1.2 q0 := by simpa only [Nat.zero_add] using priorBound
  obtain ⟨secondCost, secondBits, secondState⟩ := ExternalBits.runTotalWithResources_bound attempts
    (second before.1.1) before.1.2 q0 q0 priorBound' (Nat.le_refl _) chosen chosenReached
  obtain ⟨selectedBound⟩ := secondState
  let encoded := Cost.executeTotalCost random attempts (privateStage chosen.1.1)
    chosen.1.2 seed (q0 + q1)
  obtain ⟨_, privateCost, privateState⟩ := Cost.executeTotalCost_resources random attempts
    (privateStage chosen.1.1) chosen.1.2 seed (q0 + q1) (q0 + q1) selectedBound (Nat.le_refl _)
  have privateBits := Cost.executeTotalCost_bits random attempts
    (privateStage chosen.1.1) chosen.1.2 seed (q0 + q1)
  obtain ⟨encodedBound⟩ := privateState
  dsimp only
  intro decided decidedReached
  obtain ⟨lastCost, lastBits, lastState⟩ := ExternalBits.runTotalWithResources_bound attempts
    (last chosen.1.1 encoded.1.1) encoded.1.2.1 (q0 + q1 + privateBudget)
    (q0 + q1 + privateBudget) encodedBound (Nat.le_refl _) decided decidedReached
  have h0 : before.2.1 ≤ q0 * unit := firstCost.trans
    (Nat.mul_le_mul_left q0 (by dsimp [unit, total]; omega))
  have h1 : chosen.2.1 ≤ q1 * unit := secondCost.trans
    (Nat.mul_le_mul_left q1 (by dsimp [unit, total]; omega))
  have hp : encoded.2.2.1 ≤ privateBudget * unit := privateCost.trans
    (Nat.mul_le_mul_left privateBudget (by dsimp [unit, total]; omega))
  change decided.2.1 ≤ q2 * unit at lastCost
  refine ⟨?_, ?_, lastState⟩
  · have sum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h0 h1) hp) lastCost
    simpa only [← Nat.add_mul] using sum
  · have sum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add firstBits secondBits) privateBits) lastBits
    simpa only [← Nat.add_mul] using sum

end SimulatorMachine.PhaseCost
end Kriterion.ArgoMAC.Security
