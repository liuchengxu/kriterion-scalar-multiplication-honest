import Proof.Privacy.Source.FullGateGhostMass
import Proof.Privacy.Bounds.AdaptiveLossAccounting

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography Cryptography.Assumptions

noncomputable section

set_option exponentiation.threshold 400 in
/-- The concrete ghost-source ratio gives the checked ideal transcript error envelope. -/
theorem fullGateGhostRatio_event_bound [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    [Fintype BaseField]
    {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : NonZeroScalar) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State))
    (fallbackLength : ∀ retained source output, output ∈ (fallback retained source).support →
      (output.2.2.1 ++ output.2.2.2.2.2).length ≤
        adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter)
    (real : PMF (FullGateTranscript adversary.State))
    (ratio : ∀ transcript,
      (1 - (((186 * (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) + 508 : Nat) : ENNReal) /
        (2 : ENNReal) ^ 128)) *
        sourceGoodMass (fullGateGhostSamples adversary parameter auxiliary scalar.value witness fallback)
          (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin} transcript ≤ real transcript)
    (event : Set (FullGateTranscript adversary.State)) :
    |(real.toOuterMeasure event).toReal -
      ((idealAdaptiveTranscriptWithState (Garbling.garbledCircuit construction) Garbling.topology
        concreteCircuitSimulator circuitSimulatorOracleHandler adversary parameter scalar auxiliary).toOuterMeasure
          event).toReal| ≤
      adaptiveErrorEnvelope (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) := by
  let queries := adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter
  let loss : ENNReal := ((186 * queries + 508 : Nat) : ENNReal) / (2 : ENNReal) ^ 128
  let samples := fullGateGhostSamples adversary parameter auxiliary scalar.value witness fallback
  let kernel := fun coin : (FullGatePrefixCoin adversary.State × FullGateTranscript adversary.State) × BaseField =>
    PMF.pure coin.1.2
  let good := sourceGoodMass samples kernel {coin | fullGateGhostBad coin}
  let full := fullAdaptiveGateSource scalar.value witness parameter
    (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2)
    (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
    fallback
  have sourceLaw : samples.bind kernel = full :=
    fullGateGhostSamples_transcript adversary parameter auxiliary scalar.value witness fallback
  have goodLe : ∀ transcript, good transcript ≤ full transcript := by
    intro transcript
    rw [← sourceLaw]
    exact sourceGoodMass_le samples kernel _ transcript
  have missing := fullGateGhostGood_missing_le adversary parameter auxiliary scalar.value witness fallback fallbackLength
  have sourceBound := hCoefficient_event_of_goodSubmass real full good loss (by finiteness) _ goodLe missing ratio event
  have endpoint := fullGateSource_idealTranscript_bound adversary parameter scalar auxiliary witness fallback event
  have triangle := abs_sub_le (real.toOuterMeasure event).toReal (full.toOuterMeasure event).toReal
    ((idealAdaptiveTranscriptWithState (Garbling.garbledCircuit construction) Garbling.topology
      concreteCircuitSimulator circuitSimulatorOracleHandler adversary parameter scalar auxiliary).toOuterMeasure event).toReal
  apply (triangle.trans (add_le_add sourceBound endpoint)).trans
  have accounting := invalidCombinedLoss_le_envelope (adversary.firstQueryBudget parameter) queries
    (Nat.le_add_right _ _)
  have lossReal : loss.toReal = ((186 * queries + 508 : Nat) : ℝ) / (2 : ℝ) ^ 128 := by
    simp only [loss, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat]
  rw [lossReal]
  convert accounting using 1 <;> first | rfl |
    (simp only [queries, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]; ring)


/-- The actual decision advantage is the full-transcript decision event difference. -/
theorem adaptiveTranscriptWithState_advantage_eq
    {oracle : OracleSpec.{0, 0}} {Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle Topology State Aux : Type}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle)
    (randomTape : Nat → PMF Randomness) (realOracle : OracleHandler oracle Randomness)
    (topology : Circuit → Topology)
    (simulator : GarbledCircuit.Simulator Input Output Public Labels Topology State)
    (idealOracle : OracleHandler oracle State)
    (adversary : GarbledCircuit.AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) :
    advantage (GarbledCircuit.realGame scheme randomTape realOracle adversary parameter circuit auxiliary)
      (GarbledCircuit.idealGame scheme topology simulator idealOracle adversary parameter circuit auxiliary) =
    |((realAdaptiveTranscriptWithState scheme randomTape realOracle adversary parameter circuit auxiliary).toOuterMeasure
        {output | output.2.2.2.2.1 = true}).toReal -
      ((idealAdaptiveTranscriptWithState scheme topology simulator idealOracle adversary parameter circuit auxiliary).toOuterMeasure
        {output | output.2.2.2.2.1 = true}).toReal| := by
  have realDecision : (realAdaptiveTranscriptWithState scheme randomTape realOracle adversary
      parameter circuit auxiliary).map (fun output => output.2.2.2.2.1) =
      GarbledCircuit.realGame scheme randomTape realOracle adversary parameter circuit auxiliary := by
    rw [← realAdaptiveTranscript_decision scheme randomTape realOracle adversary parameter circuit auxiliary,
      ← realAdaptiveTranscriptWithState_erase scheme randomTape realOracle adversary parameter circuit auxiliary,
      PMF.map_comp]
    rfl
  have idealDecision : (idealAdaptiveTranscriptWithState scheme topology simulator idealOracle adversary
      parameter circuit auxiliary).map (fun output => output.2.2.2.2.1) =
      GarbledCircuit.idealGame scheme topology simulator idealOracle adversary parameter circuit auxiliary := by
    rw [← idealAdaptiveTranscript_decision scheme topology simulator idealOracle adversary parameter circuit auxiliary,
      ← idealAdaptiveTranscriptWithState_erase scheme topology simulator idealOracle adversary parameter circuit auxiliary,
      PMF.map_comp]
    rfl
  unfold advantage
  rw [← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton,
    ← realDecision, ← idealDecision, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  rfl


/-- The concrete small-budget source ratios close the universal privacy obligation. -/
theorem concreteAdaptivePrivacy_of_smallSourceRatios
    [FieldCertificate] [GroupCertificate] [TerminationCertificate] [Fintype BaseField] {Aux : Type}
    (witness : Garbling.Randomness)
    (smallRatio : ∀
      (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
      (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux),
      adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
      ∀ transcript : FullGateTranscript adversary.State,
        (1 - (((186 * (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) + 508 : Nat) : ENNReal) /
          (2 : ENNReal) ^ 128)) *
          sourceGoodMass
            (fullGateGhostSamples adversary parameter auxiliary scalar.value witness
              (fullGateRealFallback adversary parameter auxiliary scalar witness))
            (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin} transcript ≤
          (realAdaptiveTranscriptWithState (Garbling.garbledCircuit construction)
            (randomTape witness) Garbling.oracleHandler adversary parameter scalar auxiliary) transcript) :
    GarbledCircuit.ConcreteAdaptivePrivacy (Aux := Aux) (Garbling.garbledCircuit construction)
      Garbling.topology concreteCircuitSimulator (randomTape witness) Garbling.oracleHandler
      circuitSimulatorOracleHandler 100 := by
  intro adversary circuits auxiliaries parameter
  let queries := adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter
  change WorkPerAdvantage 100 (queries + 1) _
  by_cases small : queries < 2 ^ 100
  · apply adaptiveEnvelope_has100Bits queries
    rw [adaptiveTranscriptWithState_advantage_eq]
    exact fullGateGhostRatio_event_bound adversary parameter (auxiliaries parameter)
      (circuits parameter) witness
      (fullGateRealFallback adversary parameter (auxiliaries parameter) (circuits parameter) witness)
      (fullGateRealFallback_length adversary parameter (auxiliaries parameter) (circuits parameter) witness)
      (realAdaptiveTranscriptWithState (Garbling.garbledCircuit construction)
        (randomTape witness) Garbling.oracleHandler adversary parameter (circuits parameter) (auxiliaries parameter))
      (smallRatio adversary parameter (circuits parameter) (auxiliaries parameter) small) _
  · exact largeBudget_has100Bits _ _ queries (Nat.le_of_not_gt small)

end

end Kriterion.ArgoMAC.Security
