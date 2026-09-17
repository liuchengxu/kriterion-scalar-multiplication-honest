import Proof.Privacy.Source.SourcePrefixReference
import Proof.Privacy.Source.RetainedTableAlignment

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
/-- The valid selected view uses the exact retained pipeline schedule. -/
theorem validSourceView_program [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (tag : FullCircuitSource)
    (state : SimulatorState) (valid : OnCurve input)
    (enc : state.encOracle = rest.encPRFOracle) (hash : state.hashOracle = rest.hashOracle) :
    programSelectedGateView state input (key.encodeAffine input)
      (selectedGateView (circuitMaskSampleGarble rest.algebraic.field.bridgeKey
        rest.algebraic.field.curveMask.value
        (FieldMacToECMac.rowsForOutputKeys outputKeys rest.algebraic.point.pointRandomness)
        input (retainedFullSource rest tag)) input) =
    programGateSchedule state (validSourceSchedule rest outputKeys input key tag) := by
  obtain ⟨point, decoded⟩ := Option.ne_none_iff_exists'.mp ((decodePoint_defined input).mpr valid)
  simp only [selectedGateView, decoded, Option.map_some, programSelectedGateView]
  rw [circuitMaskSampleGarble_linkedSchedule state rest.algebraic.field.bridgeKey
    rest.algebraic.field.curveMask.value
    (FieldMacToECMac.rowsForOutputKeys outputKeys rest.algebraic.point.pointRandomness)
    input (retainedFullSource rest tag) key valid]
  simp only [enc, hash, validSourceSchedule]

set_option maxRecDepth 4096 in
/-- The valid tag event equals the actual selected-view source event. -/
theorem validTagGoodEvent_iff_source [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource) (labels : Garbling.Labels)
    (valid : OnCurve input) (bits : labels.input = BitInput.ofAffine input)
    (mac : key.encodeAffine input = labels.inputMac)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) :
    sample ∈ validTagGoodEvent rest outputKeys table input key
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
  have enc : (transcriptFinalState idealOracleHandler initial before).encOracle = rest.encPRFOracle :=
    (idealTranscriptFinal_oracles initial before).1
  have hash : (transcriptFinalState idealOracleHandler initial before).hashOracle = rest.hashOracle :=
    (idealTranscriptFinal_oracles initial before).2
  rw [validSourceView_program rest outputKeys input sample.2 tag
    (transcriptFinalState idealOracleHandler initial before) valid enc hash]
  have labelsEq : sourceInputLabels ⟨sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩ input = labels ↔
      sample.2.encodeAffine input = key.encodeAffine input := by
    cases labels
    dsimp only at bits mac
    simp only [sourceInputLabels, Garbling.Labels.mk.injEq, ← mac, ← bits, true_and]
  simp only [validTagGoodEvent, Set.mem_setOf_eq, initialEq, labelsEq]
  constructor
  · rintro ⟨same, complete, tableEq, good, first, last⟩
    exact ⟨complete, good, tableEq, first, same, last⟩
  · rintro ⟨complete, good, tableEq, first, same, last⟩
    exact ⟨same, complete, tableEq, good, first, last⟩

end
end Kriterion.ArgoMAC.Security
