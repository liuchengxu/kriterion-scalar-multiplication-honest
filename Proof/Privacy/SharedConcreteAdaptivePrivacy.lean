import Proof.Privacy.Bounds.SharedSourceEventBound
import Proof.Privacy.Bounds.SharedAdaptiveArithmetic
import Proof.Privacy.Collision.SharedPipelinePrefixBadMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions
noncomputable section

/-- Every complete shared transcript event satisfies the checked adaptive envelope. -/
theorem sharedAdaptiveTranscript_envelope [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter ≤ 2 ^ 101)
    (event : Set (SharedFullGateTranscript adversary.State)) :
    |((realAdaptiveTranscriptWithState sharedInternalCircuit
        (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary).toOuterMeasure event).toReal -
      ((idealAdaptiveTranscriptWithState sharedInternalCircuit Garbling.topology Shared.Simulator.simulator
        circuitSimulatorOracleHandler adversary parameter scalar auxiliary).toOuterMeasure event).toReal| ≤
      adaptiveErrorEnvelope (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) := by
  have bound := sharedAdaptiveTranscript_event_bound adversary parameter auxiliary scalar witness
    (fun _ _ => realAdaptiveTranscriptWithState sharedInternalCircuit
      (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary)
    _ (sharedFullPipelinePrefixBad_mass_le adversary parameter auxiliary scalar.value witness) small event
  apply bound.trans
  have accounting := sharedAdaptiveThreeRoundingLossSum_le_envelope
    (adversary.firstQueryBudget parameter)
    (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) (Nat.le_add_right _ _)
  convert accounting using 1 <;> first | rfl |
    (simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]; ring)

/-- Every small shared adaptive game has the checked decision advantage. -/
theorem sharedAdaptiveAdvantage_envelope [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter ≤ 2 ^ 101) :
    advantage
      (GarbledCircuit.realGame sharedInternalCircuit (uniformRandomTape Shared.Randomness witness)
        sharedRealOracleHandler adversary parameter scalar auxiliary)
      (GarbledCircuit.idealGame sharedInternalCircuit Garbling.topology Shared.Simulator.simulator
        circuitSimulatorOracleHandler adversary parameter scalar auxiliary) ≤
      adaptiveErrorEnvelope (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) := by
  letI : Fintype Block := Fintype.ofFinite Block
  rw [adaptiveTranscriptWithState_advantage_eq]
  exact sharedAdaptiveTranscript_envelope adversary parameter auxiliary scalar witness small _

/-- The exact three-slot construction satisfies the universal 100-bit adaptive privacy bound. -/
theorem sharedConcreteAdaptivePrivacy [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type} (witness : Shared.Randomness) :
    GarbledCircuit.ConcreteAdaptivePrivacy (Aux := Aux) sharedInternalCircuit Garbling.topology
      Shared.Simulator.simulator (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler
      circuitSimulatorOracleHandler 100 := by
  intro adversary circuits auxiliaries parameter
  let queries := adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter
  change WorkPerAdvantage 100 (queries + 1) _
  by_cases small : queries < 2 ^ 100
  · apply adaptiveEnvelope_has100Bits queries
    apply sharedAdaptiveAdvantage_envelope adversary parameter (auxiliaries parameter) (circuits parameter) witness
    dsimp only [queries] at small
    omega
  · exact largeBudget_has100Bits _ _ queries (Nat.le_of_not_gt small)

end
end Kriterion.ArgoMAC.Security
