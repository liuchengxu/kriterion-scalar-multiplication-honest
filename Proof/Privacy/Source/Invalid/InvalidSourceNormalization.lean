import Proof.Privacy.Source.Valid.ValidSourceNormalization
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
  fixedQueryDomainFintype transcriptOracleFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- This schedule programs exactly the curve layer of the actual invalid source. -/
def invalidSourceSchedule [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (tag : FullCircuitSource) : List GateDirective :=
  (circuitMaskSampleGarble rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask.value
    (FieldMacToECMac.rowsForOutputKeys outputKeys rest.algebraic.point.pointRandomness) input
    (retainedFullSource rest tag)).curveRequest.schedule input (key.encodeAffine input)

/-- Equal selected MACs give the same invalid programmed schedule. -/
theorem invalidSourceSchedule_rekey [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key representative : InputMacKey) (tag : FullCircuitSource)
    (same : key.encodeAffine input = representative.encodeAffine input) :
    invalidSourceSchedule rest outputKeys input key tag =
      invalidSourceSchedule rest outputKeys input representative tag := by
  simp only [invalidSourceSchedule, same]

/-- This event keeps the actual selected labels and the good programmed source. -/
def invalidTagGoodEvent [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource) : Set ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) :=
  {sample | sample.2.encodeAffine input = key.encodeAffine input ∧
    FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table ∧
    ¬ rawSourceBad (validSourceCoin rest sample.2) (retainedFullSource rest tag) input before ∧
    OracleTranscriptCompatible idealOracleHandler {initial with fixedOracle := sample.1} before ∧
    OracleTranscriptCompatible idealOracleHandler
      (programGateSchedule (transcriptFinalState idealOracleHandler {initial with fixedOracle := sample.1} before)
        (invalidSourceSchedule rest outputKeys input sample.2 tag)) after}

/-- The selected MAC makes the good flag and schedule independent of unused labels. -/
theorem invalidTagGoodEvent_rekey [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource) (invalid : ¬ OnCurve input) :
    invalidTagGoodEvent rest outputKeys table input key initial before after tag =
    {sample | sample.2.encodeAffine input = key.encodeAffine input ∧
      FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table ∧
      ¬ rawSourceBad (validSourceCoin rest key) (retainedFullSource rest tag) input before ∧
      OracleTranscriptCompatible idealOracleHandler {initial with fixedOracle := sample.1} before ∧
      OracleTranscriptCompatible idealOracleHandler
        (programGateSchedule (transcriptFinalState idealOracleHandler {initial with fixedOracle := sample.1} before)
          (invalidSourceSchedule rest outputKeys input key tag)) after} := by
  ext sample
  simp only [invalidTagGoodEvent, Set.mem_setOf_eq]
  apply and_congr_right
  intro same
  have flag := rawSourceBad_offCurve_coin (validSourceCoin rest sample.2) (validSourceCoin rest key)
    (retainedFullSource rest tag) input before invalid same
  rw [flag, invalidSourceSchedule_rekey rest outputKeys input sample.2 key tag same]


set_option maxRecDepth 4096 in
/-- The good key and fixed-oracle event has the exact conditional programmed mass. -/
theorem invalidTagGoodEvent_mass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource)
    (invalid : ¬ OnCurve input)
    (empty : initial.fixedTranscript = [])
    (enc : initial.encOracle = rest.encPRFOracle) (hash : initial.hashOracle = rest.hashOracle)
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    (nonfixed : NonFixedTranscriptCompatible rest.reference after)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      (invalidTagGoodEvent rest outputKeys table input key initial before after tag) =
    if FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table ∧
      ¬ rawSourceBad (validSourceCoin rest key) (retainedFullSource rest tag) input before then
      (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
        (fixedTranscriptFactor (transcriptFinalState idealOracleHandler initial before).fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)).map
          (fun oracle => programGateSchedule
            {transcriptFinalState idealOracleHandler initial before with fixedOracle := oracle.1}
            (invalidSourceSchedule rest outputKeys input key tag))).toOuterMeasure
          {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)}) else 0 := by
  rw [invalidTagGoodEvent_rekey rest outputKeys table input key initial before after tag invalid]
  let kept := FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table ∧
    ¬ rawSourceBad (validSourceCoin rest key) (retainedFullSource rest tag) input before
  let event := fun oracle : PermutationOracle Pipeline.FixedKeyIndex Block =>
    OracleTranscriptCompatible idealOracleHandler {initial with fixedOracle := oracle} before ∧
    OracleTranscriptCompatible idealOracleHandler
      (programGateSchedule (transcriptFinalState idealOracleHandler {initial with fixedOracle := oracle} before)
        (invalidSourceSchedule rest outputKeys input key tag)) after
  by_cases keep : kept
  · have eventEq : {sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey |
        sample.2.encodeAffine input = key.encodeAffine input ∧ FullSourceComplete tag.1 ∧
        retainedFullTable rest outputKeys tag = table ∧
        ¬ rawSourceBad (validSourceCoin rest key) (retainedFullSource rest tag) input before ∧
        event sample.1} = {sample | sample.2.encodeAffine input = key.encodeAffine input ∧ event sample.1} := by
      ext sample
      simp only [Set.mem_setOf_eq, keep.1, keep.2.1, keep.2.2, not_false_eq_true, true_and]
    rw [eventEq]
    have labelsLaw := uniform_selectedMac_event_mass input key {oracle | event oracle}
    simp only [Set.mem_setOf_eq] at labelsLaw
    rw [labelsLaw]
    rw [if_pos keep]
    apply congrArg ((Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ * ·)
    have prefixLaw := idealPrefixProgrammed_mass initial rest.reference before after
      (invalidSourceSchedule rest outputKeys input key tag) empty enc hash compatible
    apply prefixLaw.trans
    apply congrArg (fixedTranscriptFactor (transcriptFinalState idealOracleHandler initial before).fixedTranscript * ·)
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
    apply congrArg (PMF.uniformOfFintype (TranscriptOracle
      (transcriptFinalState idealOracleHandler initial before).fixedTranscript)).toOuterMeasure
    ext oracle
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    apply idealCompatible_iff_fixed_of_nonfixed _ rest.reference after
    · exact (programGateSchedule_encOracle _ _).trans
        ((idealTranscriptFinal_oracles initial before).1.trans enc)
    · exact (programGateSchedule_hashOracle _ _).trans
        ((idealTranscriptFinal_oracles initial before).2.trans hash)
    · exact nonfixed
  · rw [if_neg keep]
    apply (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
    apply Set.disjoint_left.mpr
    intro sample _ member
    exact keep ⟨member.2.1, member.2.2.1, member.2.2.2.1⟩



end
end Kriterion.ArgoMAC.Security
