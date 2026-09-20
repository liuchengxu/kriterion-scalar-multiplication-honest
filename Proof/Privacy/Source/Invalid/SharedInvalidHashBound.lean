import Proof.Privacy.Source.Invalid.SharedInvalidMaskEntrance
import Proof.Privacy.Collision.SharedHiddenLinkBad

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
set_option maxRecDepth 2048
attribute [local instance 10] Classical.propDecidable

/-- This event records a hash query at the independently retained bridge key. -/
def sharedInvalidHashEvent {Observation : Type*}
    (transcript : Observation → List (Sigma sharedRealOracleSpec.Answer)) :
    Set (Option (BaseField × Observation)) :=
  {result | ∃ bridge output, result = some (bridge, output) ∧
    bridge ∈ transcriptHashInputs (sharedLegacyTranscript (transcript output))}

/-- The independent invalid curve result leaves one field-sized target per hash query. -/
theorem sharedInvalidIndependentHash_mass_le [FieldCertificate] {Aux Observation : Type*}
    (key : InputMacKey) (state : Aux → Shared.Simulator.OracleState)
    (choose : Pipeline.Table → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Shared.Simulator.OracleState → PMF Observation)
    (transcript : Observation → List (Sigma sharedRealOracleSpec.Answer)) (budget : Nat)
    (lengthBound : ∀ table selected, selected ∈ (choose table).support →
      ∀ oracle, ∀ output ∈ (observe table selected oracle).support,
      (transcript output).length ≤ budget) :
    (((sharedInvalidCurveChoice choose).bind fun selected =>
      (PMF.uniformOfFintype (BaseField × BaseField)).bind fun pair =>
        sharedInvalidCurveObserve key state
          (fun table selected bridge oracle => (observe table selected oracle).map (Prod.mk bridge))
          (publicMaskTable selected.2.1) (selected.1, selected.2.2) pair.1
          (selected.2.1.curveRequest.retarget selected.1 pair.2)).toOuterMeasure
        (sharedInvalidHashEvent transcript)) ≤ (budget : ENNReal) / baseFieldModulus := by
  apply Probability.bind_event_le
  intro selected selectedMember
  have chosen : (selected.1, selected.2.2) ∈ (choose (publicMaskTable selected.2.1)).support := by
    simp only [sharedInvalidCurveChoice, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at selectedMember
    obtain ⟨sample, _, choice, member, same⟩ := selectedMember
    cases same
    exact member
  rw [uniform_prod_eq_bind, PMF.bind_bind]
  apply Probability.bind_event_le
  intro target targetMember
  simp only [PMF.bind_map, Function.comp_def]
  by_cases valid : OnCurve selected.1
  · simp only [sharedInvalidCurveObserve, if_pos valid, PMF.bind_const]
    simp [PMF.toOuterMeasure_pure_apply, sharedInvalidHashEvent]
  · simp only [sharedInvalidCurveObserve, if_neg valid, PMF.map_comp, Function.comp_def]
    simp only [PMF.map]
    rw [PMF.bind_comm]
    apply Probability.bind_event_le
    intro output outputMember
    change ((PMF.uniformOfFintype BaseField).map (fun bridge => some (bridge, output))).toOuterMeasure
      (sharedInvalidHashEvent transcript) ≤ _
    rw [PMF.toOuterMeasure_map_apply]
    change (PMF.uniformOfFintype BaseField).toOuterMeasure
      {bridge | ∃ bridge' output', some (bridge, output) = some (bridge', output') ∧
        bridge' ∈ transcriptHashInputs (sharedLegacyTranscript (transcript output'))} ≤ _
    have event : {bridge | ∃ bridge' output', some (bridge, output) = some (bridge', output') ∧
        bridge' ∈ transcriptHashInputs (sharedLegacyTranscript (transcript output'))} =
        {bridge | bridge ∈ transcriptHashInputs (sharedLegacyTranscript (transcript output))} := by
      ext bridge
      constructor
      · rintro ⟨bridge', output', same, member⟩
        cases Option.some.inj same
        exact member
      · intro member
        exact ⟨bridge, output, rfl, member⟩
    rw [event]
    apply (uniform_hidden_transcript_hit (sharedLegacyTranscript (transcript output))).trans
    rw [sharedLegacyTranscript_length]
    exact ENNReal.div_le_div_right (by exact_mod_cast lengthBound _ _ chosen _ output outputMember) _

/-- The actual nonzero mask adds one field-sized exception to the shared hash-hit bound. -/
theorem sharedInvalidMaskedHash_mass_le [FieldCertificate] {Aux Observation : Type*}
    (rows : FieldMacToECMac.Rows) (sparse : ∀ row, FieldMacToECMac.SparseRow (rows.get row))
    (key : InputMacKey) (state : Aux → Shared.Simulator.OracleState)
    (choose : Pipeline.Table → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Shared.Simulator.OracleState → PMF Observation)
    (transcript : Observation → List (Sigma sharedRealOracleSpec.Answer)) (budget : Nat)
    (lengthBound : ∀ table selected, selected ∈ (choose table).support →
      ∀ oracle, ∀ output ∈ (observe table selected oracle).support,
        (transcript output).length ≤ budget) :
    (((PMF.uniformOfFintype BaseField).bind fun bridge =>
      (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
        sharedInvalidCurveMaskRun bridge mask.value rows key state choose
          (fun table selected bridge oracle => (observe table selected oracle).map (Prod.mk bridge))).toOuterMeasure
        (sharedInvalidHashEvent transcript)).toReal ≤
      ((budget : ℝ) + 1) / baseFieldModulus := by
  have bound := sharedInvalidCurveMask_observation_bound rows sparse key state choose
    (fun table selected bridge oracle => (observe table selected oracle).map (Prod.mk bridge))
    (sharedInvalidHashEvent transcript)
  have independent := sharedInvalidIndependentHash_mass_le key state choose observe transcript budget lengthBound
  have finite : (budget : ENNReal) / baseFieldModulus ≠ ⊤ := by
    apply ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    norm_num [baseFieldModulus]
  have realBound := ENNReal.toReal_mono finite independent
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast] at realBound
  have difference := (abs_sub_le_iff.mp bound).2
  rw [add_div]
  linarith

end
end Kriterion.ArgoMAC.Security
