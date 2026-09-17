import Proof.Privacy.Source.Valid.ValidSourceSum
import Proof.Privacy.Source.Valid.ValidSourceKernel
import Proof.Privacy.Source.SourceRekeyGood
import Proof.Privacy.Source.SourceTranscriptCompatibility
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
  fixedQueryDomainFintype transcriptOracleFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- A selected MAC has the exact public-label density in an independent oracle event. -/
theorem uniform_selectedMac_event_mass [Fintype Block] {Oracle : Type}
    [Fintype Oracle] [Nonempty Oracle]
    (input : AffineInput) (key : InputMacKey) (event : Set Oracle) :
    (PMF.uniformOfFintype (Oracle × InputMacKey)).toOuterMeasure
      {sample | sample.2.encodeAffine input = key.encodeAffine input ∧ sample.1 ∈ event} =
    (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
      (PMF.uniformOfFintype Oracle).toOuterMeasure event := by
  have law := uniform_key_event_mass (Oracle := Oracle) (selectedKeyLabelsEquiv (inputSelectedLabelBit input))
    (inputMacCoordinateEquiv (key.encodeAffine input)) {sample | sample.1 ∈ event}
  have projection := congrArg (fun distribution : PMF Oracle => distribution.toOuterMeasure event)
    (map_uniform_prod_fst (First := Oracle) (Second := EncPRF.PermutationIndex → Block))
  simp only [PMF.toOuterMeasure_map_apply] at projection
  change (PMF.uniformOfFintype (Oracle × (EncPRF.PermutationIndex → Block))).toOuterMeasure
    {sample | sample.1 ∈ event} = (PMF.uniformOfFintype Oracle).toOuterMeasure event at projection
  rw [projection] at law
  convert law using 1
  apply congrArg (PMF.uniformOfFintype (Oracle × InputMacKey)).toOuterMeasure
  ext sample
  simp only [Set.mem_setOf_eq, selectedKeyLabels_inputMac, Equiv.apply_eq_iff_eq]

/-- Equal selected MACs give the same valid programmed schedule. -/
theorem validSourceSchedule_rekey [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key representative : InputMacKey) (tag : FullCircuitSource)
    (same : key.encodeAffine input = representative.encodeAffine input) :
    validSourceSchedule rest outputKeys input key tag =
      validSourceSchedule rest outputKeys input representative tag := by
  have point := linkedSelectedMac_rekey (validSourceCoin rest representative) key input same
  simp only [validSourceCoin, GarblingSourceRest.oracleCoin] at point
  simp only [validSourceSchedule, same, point]

/-- This event keeps the actual selected labels and the good programmed source. -/
def validTagGoodEvent [FieldCertificate] [GroupCertificate]
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
        (validSourceSchedule rest outputKeys input sample.2 tag)) after}

/-- The selected MAC makes the good flag and schedule independent of unused labels. -/
theorem validTagGoodEvent_rekey [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource) :
    validTagGoodEvent rest outputKeys table input key initial before after tag =
    {sample | sample.2.encodeAffine input = key.encodeAffine input ∧
      FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table ∧
      ¬ rawSourceBad (validSourceCoin rest key) (retainedFullSource rest tag) input before ∧
      OracleTranscriptCompatible idealOracleHandler {initial with fixedOracle := sample.1} before ∧
      OracleTranscriptCompatible idealOracleHandler
        (programGateSchedule (transcriptFinalState idealOracleHandler {initial with fixedOracle := sample.1} before)
          (validSourceSchedule rest outputKeys input key tag)) after} := by
  ext sample
  simp only [validTagGoodEvent, Set.mem_setOf_eq]
  apply and_congr_right
  intro same
  have flag := rawSourceBad_rekey (validSourceCoin rest key) sample.2 (retainedFullSource rest tag) input before same
  change rawSourceBad (validSourceCoin rest sample.2) _ _ _ ↔ _ at flag
  rw [flag, validSourceSchedule_rekey rest outputKeys input sample.2 key tag same]


/-- Fixed replies determine compatibility when the other oracle replies match. -/
theorem idealCompatible_iff_fixed_of_nonfixed (state : SimulatorState) (randomness : Garbling.Randomness)
    (history : List (Sigma Garbling.oracleSpec.Answer))
    (enc : state.encOracle = randomness.encPRFOracle) (hash : state.hashOracle = randomness.hashOracle)
    (nonfixed : NonFixedTranscriptCompatible randomness history) :
    OracleTranscriptCompatible idealOracleHandler state history ↔
      PermutationTranscriptMatches state.fixedOracle (fixedOracleTranscriptRecords history) := by
  rw [idealOracleTranscriptCompatible_iff_real state {randomness with fixedKeyOracle := state.fixedOracle}
    history rfl enc hash, realOracleTranscriptCompatible_iff, nonFixedTranscriptCompatible_update]
  exact and_iff_left nonfixed

set_option maxRecDepth 4096 in
/-- The good key and fixed-oracle event has the exact conditional programmed mass. -/
theorem validTagGoodEvent_mass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource)
    (empty : initial.fixedTranscript = [])
    (enc : initial.encOracle = rest.encPRFOracle) (hash : initial.hashOracle = rest.hashOracle)
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    (nonfixed : NonFixedTranscriptCompatible rest.reference after)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      (validTagGoodEvent rest outputKeys table input key initial before after tag) =
    if FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table ∧
      ¬ rawSourceBad (validSourceCoin rest key) (retainedFullSource rest tag) input before then
      (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
        (fixedTranscriptFactor (transcriptFinalState idealOracleHandler initial before).fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)).map
          (fun oracle => programGateSchedule
            {transcriptFinalState idealOracleHandler initial before with fixedOracle := oracle.1}
            (validSourceSchedule rest outputKeys input key tag))).toOuterMeasure
          {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)}) else 0 := by
  rw [validTagGoodEvent_rekey]
  let kept := FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table ∧
    ¬ rawSourceBad (validSourceCoin rest key) (retainedFullSource rest tag) input before
  let event := fun oracle : PermutationOracle Pipeline.FixedKeyIndex Block =>
    OracleTranscriptCompatible idealOracleHandler {initial with fixedOracle := oracle} before ∧
    OracleTranscriptCompatible idealOracleHandler
      (programGateSchedule (transcriptFinalState idealOracleHandler {initial with fixedOracle := oracle} before)
        (validSourceSchedule rest outputKeys input key tag)) after
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
      (validSourceSchedule rest outputKeys input key tag) empty enc hash compatible
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
