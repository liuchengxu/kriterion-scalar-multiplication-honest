import Proof.Privacy.Simulator.SimulatorActualCost
import Proof.Privacy.Simulator.SimulatorTotalImplementation

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions OperationalOracle
open SimulatorSampling BoundedIntegerSampling SimulatorScheduleCost
namespace SimulatorMachine.TotalImplementation
open Implementation

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
attribute [local irreducible] SimulatorRejectionCost.PositiveWidths
attribute [local irreducible] setup setupCode execute countedProgram
  SimulatorSamplingCost.onlineWithCost selected Cost.executeTotalCost

/-- The abstract resource bound uses the queries that the external phases actually execute.
This theorem does not yet bound arithmetic-machine instructions. -/
theorem actual_resources [FieldCertificate] [GroupCertificate] {Aux Seed : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (setupSeed onlineSeed : Seed) :
    let prepared := (setup 256).run random setupSeed
    let cache := prepared.1.1.1.1
    let table := prepared.1.1.1.2
    ∀ before : ExternalBits.Execution adversary.Before,
      before ∈ (ExternalBits.runActual 256
        (adversary.prepare parameter auxiliary) (initial initialMetadata) 0).support →
    ∀ chosen : ExternalBits.Execution (AffineInput × adversary.After),
      chosen ∈ (ExternalBits.runActual 256
        (adversary.chooseInput parameter table auxiliary before.value) before.state before.queries).support →
    let depth := before.queries + chosen.queries
    let encoded := execute random 256 cache chosen.value.1
      ((Garbling.garbledCircuit construction).function scalar chosen.value.1) chosen.state onlineSeed depth
    ∀ decided : ExternalBits.Execution Bool,
      decided ∈ (ExternalBits.runActual 256
        (adversary.decide parameter table encoded.1.1 auxiliary chosen.value.2) encoded.1.2.1
        (depth + 836423)).support →
      let queries := depth + decided.queries
      let n := queries + 836423
      let draws := 838390 + n
      prepared.1.1.2 + before.work + chosen.work + encoded.2.2.1 + decided.work ≤
        53788704 + n * (10 * n + 16) ∧
      prepared.2 + before.bits + chosen.bits + encoded.2.2.2 + decided.bits ≤ draws * (257 * 256) ∧
      prepared.1.1.2 + before.work + chosen.work + encoded.2.2.1 + decided.work +
        4 * (prepared.2 + before.bits + chosen.bits + encoded.2.2.2 + decided.bits) + draws ≤
          53788704 + n * (10 * n + 16) + 4 * (draws * (257 * 256)) + draws ∧
      Nonempty (Cost.StateBound decided.state n) := by
  dsimp only
  intro before beforeReached chosen chosenReached
  let prepared := (setup 256).run random setupSeed
  let sample := (SimulatorSamplingCost.onlineWithCost.total 256).run random onlineSeed
  have phase := ExternalBits.all_phases_bound 256 random sample.1.2
    (adversary.prepare parameter auxiliary)
    (fun prior => adversary.chooseInput parameter prepared.1.1.1.2 auxiliary prior)
    (fun selectedInput => countedProgram prepared.1.1.1.1 selectedInput.1
      ((Garbling.garbledCircuit construction).function scalar selectedInput.1) sample.1.1.1)
    (fun selectedInput result => adversary.decide parameter prepared.1.1.1.2 result.1 auxiliary selectedInput.2)
    before beforeReached chosen chosenReached
  intro decided decidedReached
  simp only [execute] at decidedReached
  have closed := phase decided decidedReached
  have setupWork := setup_work random 256 setupSeed
  have onlineWork := execute_local random 256 prepared.1.1.1.1 chosen.value.1
    ((Garbling.garbledCircuit construction).function scalar chosen.value.1) chosen.state onlineSeed
    (before.queries + chosen.queries)
  have setupBits := setup_bits random 256 setupSeed
  have onlineBits := Code.total_bits random 256 SimulatorSamplingCost.onlineWithCost
    SimulatorSamplingCost.online_size onlineSeed
  have totalWork := Nat.add_le_add (Nat.add_le_add_right setupWork 51183699) closed.1
  have totalBits := Nat.add_le_add (Nat.add_le_add setupBits onlineBits) closed.2.1
  simp only [execute, prepared] at onlineWork ⊢
  dsimp only [sample, prepared] at closed totalWork totalBits
  have reordered : before.queries + chosen.queries + 836423 + decided.queries =
      before.queries + chosen.queries + decided.queries + 836423 := by omega
  rw [reordered] at closed totalWork totalBits
  simp only [Nat.add_mul] at totalBits
  refine ⟨?_, ?_, ?_, closed.2.2⟩ <;> omega

end SimulatorMachine.TotalImplementation
end Kriterion.ArgoMAC.Security
