import Proof.Privacy.Source.RetainedMissPhaseMass
import Proof.Privacy.Source.RetainedTableAlignment
import Proof.Privacy.Source.Invalid.InvalidSourceNormalization
import Proof.Privacy.Source.SourcePrefixReference

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The sampled fixed oracle gives the exact retained initial source state. -/
theorem initialSourceOracle_oracleKey [FieldCertificate] [GroupCertificate] (reference : SimulatorState) (rest : GarblingSourceRest)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) :
    initialSourceOracle (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.2 =
      {sourcePrefixReference reference rest with fixedOracle := sample.1} := rfl

/-- The sampled input key gives the exact retained labels. -/
theorem sourceInputLabels_oracleKey [FieldCertificate] [GroupCertificate] (rest : GarblingSourceRest)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) (input : AffineInput) :
    sourceInputLabels (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.2 input =
      (⟨BitInput.ofAffine input, sample.2.encodeAffine input⟩ : Garbling.Labels) := rfl

/-- The invalid flag ignores the sampled fixed oracle. -/
theorem rawSourceBad_oracleKey [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
    (source : CircuitMaskSample) (input : AffineInput)
    (before : List (Sigma Garbling.oracleSpec.Answer)) :
    rawSourceBad
      (simulatorSourceEquiv
        ((maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2,
          defaultSimulatorCoin.tableSample)).1 source input before ↔
      rawSourceBad (validSourceCoin rest sample.2) source input before := Iff.rfl

/-- The invalid source programs exactly its actual retained curve schedule. -/
theorem programSelectedGateView_oracleKey [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (rest : GarblingSourceRest)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
    (tag : FullCircuitSource) (input : AffineInput) (state : SimulatorState)
    (invalid : ¬ OnCurve input) :
    programSelectedGateView state input (sample.2.encodeAffine input)
      (selectedGateView
        (circuitMaskSampleGarble
          (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.1.1
          (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.1.2.value
          (retainedSourceRows scalar (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest)))) input
          (decodeFullSource (tag.1, sharedCircuitHashRest
            (garblingOracleKeyEquiv.symm (sample, rest)) tag.2))) input) =
    programGateSchedule state (invalidSourceSchedule rest
      (outputKeys construction scalar rest.reference.offsets) input sample.2 tag) := by
  rw [retainedSourceRows_oracleKey, sharedCircuitHashRest_oracleKey]
  have none : decodePoint input = none := by
    exact Classical.not_not.mp (fun nonzero => invalid ((decodePoint_defined input).mp nonzero))
  simp only [selectedGateView, none, Option.map_none, programSelectedGateView]
  rfl

set_option maxRecDepth 4096 in
/-- The invalid tag event equals the actual selected-view source event. -/
theorem invalidTagGoodEvent_iff_source [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource) (labels : Garbling.Labels)
    (invalid : ¬ OnCurve input) (bits : labels.input = BitInput.ofAffine input)
    (mac : key.encodeAffine input = labels.inputMac)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) :
    sample ∈ invalidTagGoodEvent rest outputKeys table input key
      (sourcePrefixReference reference rest) before after tag ↔
    FullSourceComplete tag.1 ∧
    ¬ rawSourceBad (validSourceCoin rest sample.2) (retainedFullSource rest tag) input before ∧
    retainedFullTable rest outputKeys tag = table ∧
    OracleTranscriptCompatible idealOracleHandler
      (initialSourceOracle ⟨sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩) before ∧
    sourceInputLabels ⟨sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩ input = labels ∧
    OracleTranscriptCompatible idealOracleHandler
      (programSelectedGateView
        (transcriptFinalState idealOracleHandler
          (initialSourceOracle ⟨sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩) before)
        input (sample.2.encodeAffine input)
        (selectedGateView (circuitMaskSampleGarble rest.algebraic.field.bridgeKey
          rest.algebraic.field.curveMask.value
          (FieldMacToECMac.rowsForOutputKeys outputKeys rest.algebraic.point.pointRandomness)
          input (retainedFullSource rest tag)) input)) after := by
  let initial := initialSourceOracle (⟨sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩ : GarblingOracleData)
  have initialEq : {sourcePrefixReference reference rest with fixedOracle := sample.1} = initial := rfl
  have decoded : decodePoint input = none :=
    Classical.not_not.mp (fun nonzero => invalid ((decodePoint_defined input).mp nonzero))
  simp only [selectedGateView, decoded, Option.map_none, programSelectedGateView]
  change _ ↔ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
    OracleTranscriptCompatible idealOracleHandler
      (programGateSchedule (transcriptFinalState idealOracleHandler initial before)
        (invalidSourceSchedule rest outputKeys input sample.2 tag)) after
  have labelsEq : sourceInputLabels ⟨sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩ input = labels ↔
      sample.2.encodeAffine input = key.encodeAffine input := by
    cases labels
    dsimp only at bits mac
    simp only [sourceInputLabels, Garbling.Labels.mk.injEq, ← mac, ← bits, true_and]
  simp only [invalidTagGoodEvent, Set.mem_setOf_eq, initialEq, labelsEq]
  constructor
  · rintro ⟨same, complete, tableEq, good, first, last⟩
    exact ⟨complete, good, tableEq, first, same, last⟩
  · rintro ⟨complete, good, tableEq, first, same, last⟩
    exact ⟨same, complete, tableEq, good, first, last⟩

end
end Kriterion.ArgoMAC.Security
