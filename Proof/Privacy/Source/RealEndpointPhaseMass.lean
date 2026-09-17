import Proof.Privacy.Source.CrossSourceMass
import Proof.Privacy.Source.RealSourceLower
import Proof.Privacy.Source.SourceReferenceSupport

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The real transcript has the common phase factors and the exact public source event. -/
theorem realAdaptiveTranscript_mass_factor [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : NonZeroScalar) (witness : Garbling.Randomness)
    (table : Pipeline.Table) (referenceBefore referenceAfter : SimulatorState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    (realAdaptiveTranscriptWithState (Garbling.garbledCircuit construction)
      (randomTape witness) Garbling.oracleHandler adversary parameter scalar auxiliary)
        (table, selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter table auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
    (if labels.input = BitInput.ofAffine selected.1 then
      (randomTape witness parameter).toOuterMeasure {randomness |
        Pipeline.garble (FieldMacToECMac.outputKeys construction scalar.value randomness.offsets)
          randomness.pointRandomness randomness.bridgeKey randomness.curveMask randomness.curveR1
          randomness.curveR2 randomness.fixedKeyOracle randomness.encPRFOracle randomness.hashOracle
          randomness.inputMacKey = table ∧
        randomness.inputMacKey.encodeAffine selected.1 = labels.inputMac ∧
        OracleTranscriptCompatible Garbling.oracleHandler randomness (before ++ after)}
      else 0) := by
  rw [realAdaptiveTranscriptWithState,
    sampledTwoPhaseTranscript_mass_factor_cross Garbling.oracleHandler idealOracleHandler
      (randomTape witness parameter)
      (fun randomness => ((Garbling.garbledCircuit construction).garble parameter scalar randomness).1) id
      (fun table => adversary.chooseInput parameter table auxiliary)
      (fun randomness state selected => PMF.pure
        ((Garbling.garbledCircuit construction).encode
          ((Garbling.garbledCircuit construction).garble parameter scalar randomness).2 selected.1, state))
      (fun table selected labels => adversary.decide parameter table labels auxiliary selected.2)
      referenceBefore referenceAfter table selected labels decision before after firstCompatible secondCompatible,
    sampledTwoPhaseSourceMass_real]
  congr 1
  have labelsEq (randomness : Garbling.Randomness) :
      (Garbling.garbledCircuit construction).encode
        ((Garbling.garbledCircuit construction).garble parameter scalar randomness).2 selected.1 = labels ↔
      labels.input = BitInput.ofAffine selected.1 ∧
        randomness.inputMacKey.encodeAffine selected.1 = labels.inputMac := by
    cases labels
    simp only [Garbling.garbledCircuit, Garbling.garble, Garbling.encode,
      Garbling.Labels.mk.injEq, InputMacKey.encodeAffine, eq_comm]
  by_cases same : labels.input = BitInput.ofAffine selected.1
  · rw [if_pos same]
    congr 1
    ext randomness
    simp only [Set.mem_setOf_eq, labelsEq, same, true_and]
    rfl
  · rw [if_neg same]
    have empty : {randomness : Garbling.Randomness |
        ((Garbling.garbledCircuit construction).garble parameter scalar randomness).1 = table ∧
        (Garbling.garbledCircuit construction).encode
          ((Garbling.garbledCircuit construction).garble parameter scalar randomness).2 selected.1 = labels ∧
        OracleTranscriptCompatible Garbling.oracleHandler (id randomness) (before ++ after)} = ∅ := by
      ext randomness
      simp only [Set.mem_setOf_eq, labelsEq, same, false_and, and_false, Set.mem_empty_iff_false]
    rw [empty]
    simp

/-- A nonzero prefix good mass contains the selected input bits. -/
theorem fullGatePrefixGood_inputBits [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State)
    (nonzero : sourceGoodMass
      (fullGatePrefixSamples scalar witness parameter
        (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2))
      (fullGatePrefixKernel scalar
        (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback) {coin | fullGatePrefixBad coin} output ≠ 0) :
    output.2.2.2.1.input = BitInput.ofAffine output.2.1.1 := by
  obtain ⟨sample, sampleMember, good, member⟩ := sourceGoodMass_support _ _ _ output nonzero
  have complete : FullSourceComplete sample.2.1.1 := not_not.mp (not_or.mp good).1
  simp only [fullGatePrefixSamples, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at sampleMember
  obtain ⟨randomness, _, tag, _, selected, _, rfl⟩ := sampleMember
  simp only [fullGatePrefixKernel, complete, if_true, gateSourceObserve,
    PMF.mem_support_map_iff] at member
  obtain ⟨last, _, rfl⟩ := member
  rfl

/-- A nonzero ghost good mass contains the selected input bits. -/
theorem fullGateGhostGood_inputBits [FieldCertificate] [GroupCertificate] [Fintype BaseField] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State)
    (nonzero : sourceGoodMass (fullGateGhostSamples adversary parameter auxiliary scalar witness fallback)
      (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin} output ≠ 0) :
    output.2.2.2.1.input = BitInput.ofAffine output.2.1.1 := by
  apply fullGatePrefixGood_inputBits adversary parameter auxiliary scalar witness fallback output
  intro zero
  apply nonzero
  apply le_antisymm
  · exact (fullGateGhostGood_le_prefixGood adversary parameter auxiliary scalar witness fallback output).trans_eq zero
  · exact bot_le

end
end Kriterion.ArgoMAC.Security
