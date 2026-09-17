import Proof.Privacy.Source.Invalid.InvalidNonfixedRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
  instDecidableEqRawCircuitGate_1 fixedQueryDomainFintype transcriptOracleFintype
attribute [local instance] instNonemptyInputMacKey_proof_8

/-- Equal replies preserve the recorded state when the nonfixed oracles change. -/
theorem idealHandler_updateNonfixed (state : SimulatorState)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle)
    (query : Garbling.oracleSpec.Query)
    (same : (idealOracleHandler query {state with encOracle := enc, hashOracle := hash}).1 =
      (idealOracleHandler query state).1) :
    (idealOracleHandler query {state with encOracle := enc, hashOracle := hash}).2 =
      {(idealOracleHandler query state).2 with encOracle := enc, hashOracle := hash} := by
  cases query <;>
    simp only [idealOracleHandler, oracleHandlerFor, recordFixed, recordEnc, recordHash] at same ⊢
  all_goals try rw [same]

/-- Compatible prefixes keep the same records under a nonfixed oracle update. -/
theorem idealTranscriptFinal_updateNonfixed (state : SimulatorState)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle)
    (history : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler state history)
    (updated : OracleTranscriptCompatible idealOracleHandler {state with encOracle := enc, hashOracle := hash} history) :
    transcriptFinalState idealOracleHandler {state with encOracle := enc, hashOracle := hash} history =
      {transcriptFinalState idealOracleHandler state history with encOracle := enc, hashOracle := hash} := by
  induction history generalizing state with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨query, answer⟩
    change _ ∧ _ at compatible updated
    have next := idealHandler_updateNonfixed state enc hash query (updated.1.trans compatible.1.symm)
    simp only [transcriptFinalState]
    rw [next]
    apply ih _ compatible.2
    rw [← next]
    exact updated.2

/-- A fixed slot program does not use either nonfixed oracle. -/
theorem programFixedSlot_updateNonfixed (state : SimulatorState)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (slot : Pipeline.FixedKeySlot) (label block : Block) :
    programFixedSlot {state with encOracle := enc, hashOracle := hash} location window slot label block =
      {programFixedSlot state location window slot label block with encOracle := enc, hashOracle := hash} := by
  unfold programFixedSlot tryProgramFixed
  split <;> rfl

/-- A selected schedule keeps its fixed behavior under a nonfixed oracle update. -/
theorem programGateSchedule_updateNonfixed (state : SimulatorState)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle)
    (schedule : List GateDirective) :
    programGateSchedule {state with encOracle := enc, hashOracle := hash} schedule =
      {programGateSchedule state schedule with encOracle := enc, hashOracle := hash} := by
  have gate (current : SimulatorState) (directive : GateDirective) :
      directive.apply {current with encOracle := enc, hashOracle := hash} =
        {directive.apply current with encOracle := enc, hashOracle := hash} := by
    unfold GateDirective.apply programGateForTarget programGate
    split <;> simp only [programPadGate, programHashGate, programFixedSlot_updateNonfixed]
  induction schedule generalizing state with
  | nil => rfl
  | cons directive tail ih =>
    change programGateSchedule (directive.apply {state with encOracle := enc, hashOracle := hash}) tail = _
    rw [gate]
    exact ih _

/-- The invalid source schedule does not read the nonfixed oracle functions. -/
theorem invalidSourceSchedule_nonfixed [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (tag : FullCircuitSource)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle) :
    invalidSourceSchedule {rest with encPRFOracle := enc, hashOracle := hash} outputKeys input key tag =
      invalidSourceSchedule rest outputKeys input key tag := rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
/-- The invalid programmed fixed mass does not read the nonfixed oracle functions. -/
theorem invalidFixedProgrammedMass_nonfixed [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (tag : FullCircuitSource)
    (state : SimulatorState) (after : List (Sigma Garbling.oracleSpec.Answer))
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle)
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    invalidFixedProgrammedMass {rest with encPRFOracle := enc, hashOracle := hash}
        outputKeys input key tag {state with encOracle := enc, hashOracle := hash} after =
      invalidFixedProgrammedMass rest outputKeys input key tag state after := by
  unfold invalidFixedProgrammedMass
  apply congrArg ((Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ * ·)
  apply congrArg (fixedTranscriptFactor state.fixedTranscript * ·)
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  apply congrArg (PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).toOuterMeasure
  ext oracle
  simp only [Set.mem_preimage, Set.mem_setOf_eq, invalidSourceSchedule_nonfixed]
  have law := programGateSchedule_updateNonfixed {state with fixedOracle := oracle.1} enc hash
    (invalidSourceSchedule rest outputKeys input key tag)
  have fixed := congrArg SimulatorState.fixedOracle law
  exact Iff.of_eq (congrArg (fun oracle => PermutationTranscriptMatches oracle (fixedOracleTranscriptRecords after)) fixed)


/-- Every retained invalid event satisfies both nonfixed transcript segments. -/
theorem invalidTagGoodEvent_nonfixed [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource)
    (enc : initial.encOracle = rest.encPRFOracle) (hash : initial.hashOracle = rest.hashOracle)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
    (member : sample ∈ invalidTagGoodEvent rest outputKeys table input key initial before after tag) :
    NonFixedTranscriptCompatible rest.reference (before ++ after) := by
  apply (nonFixedTranscriptCompatible_append rest.reference before after).mpr
  refine ⟨idealTranscript_nonfixed {initial with fixedOracle := sample.1} rest.reference before enc hash member.2.2.2.2.1, ?_⟩
  apply idealTranscript_nonfixed _ rest.reference after _ _ member.2.2.2.2.2
  · exact (programGateSchedule_encOracle _ _).trans
      ((idealTranscriptFinal_oracles _ before).1.trans enc)
  · exact (programGateSchedule_hashOracle _ _).trans
      ((idealTranscriptFinal_oracles _ before).2.trans hash)

/-- An incompatible nonfixed transcript has zero invalid event mass. -/
theorem invalidTagGoodEvent_mass_zero [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource)
    (enc : initial.encOracle = rest.encPRFOracle) (hash : initial.hashOracle = rest.hashOracle)
    (incompatible : ¬ NonFixedTranscriptCompatible rest.reference (before ++ after)) :
    (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      (invalidTagGoodEvent rest outputKeys table input key initial before after tag) = 0 := by
  apply (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
  apply Set.disjoint_left.mpr
  intro sample _ member
  exact incompatible (invalidTagGoodEvent_nonfixed rest outputKeys table input key initial before after tag enc hash sample member)

/-- The retained full source does not read the nonfixed oracle functions. -/
theorem retainedFullSource_nonfixed [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (tag : FullCircuitSource)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle) :
    retainedFullSource {rest with encPRFOracle := enc, hashOracle := hash} tag =
      retainedFullSource rest tag := rfl

/-- An invalid source keeps its actual good flag when the nonfixed oracles change. -/
theorem invalidSourceGood_nonfixed [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (key : InputMacKey) (tag : FullCircuitSource)
    (input : AffineInput) (before : List (Sigma Garbling.oracleSpec.Answer))
    (invalid : ¬ OnCurve input)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle) :
    (¬ rawSourceBad (validSourceCoin {rest with encPRFOracle := enc, hashOracle := hash} key)
        (retainedFullSource {rest with encPRFOracle := enc, hashOracle := hash} tag) input before) ↔
      ¬ rawSourceBad (validSourceCoin rest key) (retainedFullSource rest tag) input before := by
  rw [retainedFullSource_nonfixed]
  exact not_congr (rawSourceBad_offCurve_coin _ _ _ _ _ invalid rfl)

/-- Equal states give the same conditional fixed mass. -/
theorem invalidFixedProgrammedMass_congr_state [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (tag : FullCircuitSource)
    (state other : SimulatorState) (after : List (Sigma Garbling.oracleSpec.Answer))
    [Nonempty (TranscriptOracle state.fixedTranscript)] [Nonempty (TranscriptOracle other.fixedTranscript)]
    (same : state = other) :
    invalidFixedProgrammedMass rest outputKeys input key tag state after =
      invalidFixedProgrammedMass rest outputKeys input key tag other after := by
  cases same
  rfl

private theorem guarded_value_congr (first second : Prop) [Decidable first] [Decidable second]
    (left right : ℝ≥0∞) (condition : first ↔ second) (value : left = right) :
    (if first then left else 0) = if second then right else 0 := by
  by_cases keep : first
  · simp only [if_pos keep, if_pos (condition.mp keep), value]
  · simp only [if_neg keep, if_neg (mt condition.mpr keep)]

private theorem invalidProgrammed_formula_eq [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (tag : FullCircuitSource)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
      (fixedTranscriptFactor (transcriptFinalState idealOracleHandler initial before).fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)).map
          (fun oracle => programGateSchedule
            {transcriptFinalState idealOracleHandler initial before with fixedOracle := oracle.1}
            (invalidSourceSchedule rest outputKeys input key tag))).toOuterMeasure
          {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)}) =
      invalidFixedProgrammedMass rest outputKeys input key tag
        (transcriptFinalState idealOracleHandler initial before) after := by
  unfold invalidFixedProgrammedMass
  apply congrArg ((Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ * ·)
  apply congrArg (fixedTranscriptFactor (transcriptFinalState idealOracleHandler initial before).fixedTranscript * ·)
  apply congrArg (fun samples : PMF SimulatorState => samples.toOuterMeasure
    {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)})
  apply congrArg (PMF.uniformOfFintype (TranscriptOracle
    (transcriptFinalState idealOracleHandler initial before).fixedTranscript)).map
  funext oracle
  rfl

set_option maxRecDepth 4096 in
/-- The final prefix state gives the exact invalid event mass. -/
def invalidTagGoodEvent_mass_named [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource) (invalid : ¬ OnCurve input)
    (empty : initial.fixedTranscript = [])
    (enc : initial.encOracle = rest.encPRFOracle) (hash : initial.hashOracle = rest.hashOracle)
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    (nonfixed : NonFixedTranscriptCompatible rest.reference after)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :=
  let law := invalidTagGoodEvent_mass rest outputKeys table input key initial before after tag invalid
    empty enc hash compatible nonfixed
  law.trans (guarded_value_congr _ _ _ _ Iff.rfl
    (invalidProgrammed_formula_eq rest outputKeys input key tag initial before after))

set_option maxRecDepth 4096 in
/-- A compatible nonfixed update preserves the normalized invalid fixed mass. -/
theorem invalidTagGoodEvent_mass_updateNonfixed [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource) (invalid : ¬ OnCurve input) (empty : initial.fixedTranscript = [])
    (initialEnc : initial.encOracle = rest.encPRFOracle) (initialHash : initial.hashOracle = rest.hashOracle)
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle)
    (nonfixed : NonFixedTranscriptCompatible {rest with encPRFOracle := enc, hashOracle := hash}.reference (before ++ after))
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      (invalidTagGoodEvent {rest with encPRFOracle := enc, hashOracle := hash} outputKeys table input key
        {initial with encOracle := enc, hashOracle := hash} before after tag) =
    if FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table ∧
      ¬ rawSourceBad (validSourceCoin rest key) (retainedFullSource rest tag) input before then
      invalidFixedProgrammedMass rest outputKeys input key tag
        (transcriptFinalState idealOracleHandler initial before) after else 0 := by
  have segments := (nonFixedTranscriptCompatible_append _ before after).mp nonfixed
  have real := (idealOracleTranscriptCompatible_iff_real initial
    {rest.reference with fixedKeyOracle := initial.fixedOracle} before rfl initialEnc initialHash).mp compatible
  have fixed := (realOracleTranscriptCompatible_iff _ before).mp real |>.1
  have updated : OracleTranscriptCompatible idealOracleHandler
      {initial with encOracle := enc, hashOracle := hash} before := by
    apply (idealOracleTranscriptCompatible_iff_real _
      {{rest with encPRFOracle := enc, hashOracle := hash}.reference with fixedKeyOracle := initial.fixedOracle}
      before rfl rfl rfl).mpr
    rw [realOracleTranscriptCompatible_iff, nonFixedTranscriptCompatible_update]
    exact ⟨fixed, segments.1⟩
  have finalEq := idealTranscriptFinal_updateNonfixed initial enc hash before compatible updated
  letI : Nonempty (TranscriptOracle
      (transcriptFinalState idealOracleHandler {initial with encOracle := enc, hashOracle := hash} before).fixedTranscript) := by
    rw [finalEq]
    exact inferInstanceAs (Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript))
  have mass := invalidTagGoodEvent_mass_named
    {rest with encPRFOracle := enc, hashOracle := hash} outputKeys table input key
    {initial with encOracle := enc, hashOracle := hash}
    before after tag invalid empty rfl rfl updated segments.2
  apply mass.trans
  apply guarded_value_congr
  · simp only [retainedFullTable_nonfixed, invalidSourceGood_nonfixed rest key tag input before invalid enc hash]
  · apply (invalidFixedProgrammedMass_congr_state
      {rest with encPRFOracle := enc, hashOracle := hash} outputKeys input key tag _ _ after finalEq).trans
    exact invalidFixedProgrammedMass_nonfixed rest outputKeys input key tag _ after enc hash

/-- Updating the source rest gives the same actual oracle reference. -/
theorem sourceReference_updateNonfixed (rest : GarblingSourceRest)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle) :
    {rest with encPRFOracle := enc, hashOracle := hash}.reference =
      nonfixedSourceReference rest.reference enc hash := rfl

set_option maxRecDepth 4096 in
/-- The exact invalid event mass factors through the complete nonfixed transcript guard. -/
theorem invalidTagGoodEvent_mass_nonfixed_factor [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource) (invalid : ¬ OnCurve input) (empty : initial.fixedTranscript = [])
    (initialEnc : initial.encOracle = rest.encPRFOracle) (initialHash : initial.hashOracle = rest.hashOracle)
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      (invalidTagGoodEvent {rest with encPRFOracle := enc, hashOracle := hash} outputKeys table input key
        {initial with encOracle := enc, hashOracle := hash} before after tag) =
    if NonFixedTranscriptCompatible (nonfixedSourceReference rest.reference enc hash) (before ++ after) then
      if FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table ∧
        ¬ rawSourceBad (validSourceCoin rest key) (retainedFullSource rest tag) input before then
        invalidFixedProgrammedMass rest outputKeys input key tag
          (transcriptFinalState idealOracleHandler initial before) after else 0 else 0 := by
  by_cases keep : NonFixedTranscriptCompatible (nonfixedSourceReference rest.reference enc hash) (before ++ after)
  · rw [if_pos keep]
    exact invalidTagGoodEvent_mass_updateNonfixed rest outputKeys table input key initial before after tag
      invalid empty initialEnc initialHash compatible enc hash
      (by rwa [sourceReference_updateNonfixed])
  · rw [if_neg keep]
    exact invalidTagGoodEvent_mass_zero {rest with encPRFOracle := enc, hashOracle := hash}
      outputKeys table input key {initial with encOracle := enc, hashOracle := hash} before after tag rfl rfl
      (by rwa [sourceReference_updateNonfixed])

end
end Kriterion.ArgoMAC.Security
