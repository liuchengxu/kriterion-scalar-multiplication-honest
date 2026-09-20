import Proof.Privacy.Source.CrossSourceMass
import Proof.Privacy.Source.SharedRealSourceLower
import Proof.Privacy.Simulator.SharedSimulator

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- This internal view retains input bits beside the selected shared labels. -/
def sharedInternalCircuit [FieldCertificate] [GroupCertificate] :
    GarbledCircuit NonZeroScalar AffineInput (Option Point) Shared.Randomness Pipeline.Table
      Garbling.EncodingKey Garbling.Labels
      (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) := {
  function := (Garbling.garbledCircuit construction).function
  garble := fun parameter scalar tape => (Garbling.garbledCircuit construction).garble parameter scalar tape.val
  encode := (Garbling.garbledCircuit construction).encode
  evaluate := fun oracle => (Garbling.garbledCircuit construction).evaluate (Shared.expandOracle oracle.1, oracle.2)
}

/-- The shared real transcript has its two program factors and its actual public source event. -/
theorem sharedRealAdaptiveTranscript_mass_factor [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (table : Pipeline.Table) (referenceBefore referenceAfter : Shared.Simulator.OracleState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma sharedRealOracleSpec.Answer))
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    (realAdaptiveTranscriptWithState sharedInternalCircuit
      (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary)
        (table, selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter table auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
    (if labels.input = BitInput.ofAffine selected.1 then
      (uniformRandomTape Shared.Randomness witness parameter).toOuterMeasure {randomness |
        Pipeline.garble (FieldMacToECMac.outputKeys construction scalar.value randomness.val.offsets)
          randomness.val.pointRandomness randomness.val.bridgeKey randomness.val.curveMask randomness.val.curveR1
          randomness.val.curveR2 randomness.val.fixedKeyOracle randomness.val.encPRFOracle randomness.val.hashOracle
          randomness.val.inputMacKey = table ∧
        randomness.val.inputMacKey.encodeAffine selected.1 = labels.inputMac ∧
        OracleTranscriptCompatible sharedRealOracleHandler randomness (before ++ after)}
      else 0) := by
  rw [realAdaptiveTranscriptWithState,
    sampledTwoPhaseTranscript_mass_factor_cross sharedRealOracleHandler idealOracleHandler
      (uniformRandomTape Shared.Randomness witness parameter)
      (fun randomness => (sharedInternalCircuit.garble parameter scalar randomness).1) id
      (fun table => adversary.chooseInput parameter table auxiliary)
      (fun randomness state selected => PMF.pure
        (sharedInternalCircuit.encode (sharedInternalCircuit.garble parameter scalar randomness).2 selected.1, state))
      (fun table selected labels => adversary.decide parameter table labels auxiliary selected.2)
      referenceBefore referenceAfter table selected labels decision before after firstCompatible secondCompatible,
    sampledTwoPhaseSourceMass_real]
  apply congrArg ((((runOracleProgramWithTranscript idealOracleHandler
    (adversary.chooseInput parameter table auxiliary) referenceBefore).map
      (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after)) * ·)
  have labelsEq (randomness : Shared.Randomness) :
      sharedInternalCircuit.encode (sharedInternalCircuit.garble parameter scalar randomness).2 selected.1 = labels ↔
      labels.input = BitInput.ofAffine selected.1 ∧
        randomness.val.inputMacKey.encodeAffine selected.1 = labels.inputMac := by
    cases labels
    simp only [sharedInternalCircuit, Garbling.garbledCircuit, Garbling.garble, Garbling.encode,
      Garbling.Labels.mk.injEq, InputMacKey.encodeAffine, eq_comm]
  by_cases same : labels.input = BitInput.ofAffine selected.1
  · rw [if_pos same]
    apply congrArg (uniformRandomTape Shared.Randomness witness parameter).toOuterMeasure
    ext randomness
    simp only [Set.mem_setOf_eq, labelsEq, same, true_and]
    rfl
  · rw [if_neg same]
    have empty : {randomness : Shared.Randomness |
        (sharedInternalCircuit.garble parameter scalar randomness).1 = table ∧
        sharedInternalCircuit.encode (sharedInternalCircuit.garble parameter scalar randomness).2 selected.1 = labels ∧
        OracleTranscriptCompatible sharedRealOracleHandler (id randomness) (before ++ after)} = ∅ := by
      ext randomness
      simp only [Set.mem_setOf_eq, labelsEq, same, false_and, and_false, Set.mem_empty_iff_false]
    rw [empty]
    simp

/-- The retained shared source gives the exact public event in the real transcript. -/
theorem sharedRealAdaptiveTranscript_retained_factor [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (table : Pipeline.Table) (referenceBefore referenceAfter : Shared.Simulator.OracleState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (key : InputMacKey)
    (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    (realAdaptiveTranscriptWithState sharedInternalCircuit
      (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary)
        (table, selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter table auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
    (uniformRandomTape Shared.Randomness witness parameter).toOuterMeasure {randomness |
      Pipeline.garble (FieldMacToECMac.outputKeys construction scalar.value
        (sharedGarblingOracleKeyEquiv randomness).2.reference.offsets)
        randomness.val.pointRandomness randomness.val.bridgeKey randomness.val.curveMask randomness.val.curveR1
        randomness.val.curveR2 randomness.val.fixedKeyOracle randomness.val.encPRFOracle randomness.val.hashOracle
        randomness.val.inputMacKey = table ∧
      randomness.val.inputMacKey.encodeAffine selected.1 = key.encodeAffine selected.1 ∧
      OracleTranscriptCompatible sharedRealOracleHandler randomness (before ++ after)} := by
  rw [sharedRealAdaptiveTranscript_mass_factor adversary parameter auxiliary scalar witness table
    referenceBefore referenceAfter selected labels decision before after firstCompatible secondCompatible,
    if_pos bits]
  rw [mac]
  rfl

end
end Kriterion.ArgoMAC.Security
