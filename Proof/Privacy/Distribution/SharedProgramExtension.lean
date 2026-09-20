import Proof.Privacy.Distribution.SharedProgrammingDistribution

namespace Kriterion.ArgoMAC.Shared.Simulator
open BN254 Cryptography Security
open scoped ENNReal
noncomputable section
attribute [local instance] transcriptOracleFintype

/-- A positive programmed-query event supplies its own transcript extension. -/
theorem commands_extension_of_mass_ne_zero [Fintype Block]
    (state : OracleState) (values : List FixedCommand)
    (queries : List (PermutationRecord FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript (commandRecords values))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (positive : ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
      (fun oracle => commands {state with fixedOracle := oracle.1} values)).toOuterMeasure
        {programmed | PermutationTranscriptMatches programmed.fixedOracle queries} ≠ 0) :
    Nonempty (TranscriptOracle
      (programRecordHistory state.fixedTranscript (commandRecords values) ++ queries)) := by
  have intersects : ¬ Disjoint
      (((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
        (fun oracle => commands {state with fixedOracle := oracle.1} values)).support)
      {programmed | PermutationTranscriptMatches programmed.fixedOracle queries} := by
    rwa [← PMF.toOuterMeasure_apply_eq_zero_iff]
  obtain ⟨programmed, supported, matching⟩ := Set.not_disjoint_iff.mp intersects
  simp only [PMF.mem_support_map_iff] at supported
  obtain ⟨oracle, _, rfl⟩ := supported
  rw [commands_state state values fresh oracle] at matching
  let extended := programTranscriptRecords state.fixedTranscript (commandRecords values) fresh oracle
  refine ⟨⟨extended.1, ?_⟩⟩
  intro record member
  rcases List.mem_append.mp member with before | after
  · exact extended.2 record before
  · exact matching record after

/-- A zero query mass needs no extension witness. -/
theorem commands_mass_lower_of_extension [Fintype Block]
    (state : OracleState) (values : List FixedCommand)
    (queries : List (PermutationRecord FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript (commandRecords values))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (lower : ℝ≥0∞ → ℝ≥0∞) (atZero : lower 0 = 0) (target : ℝ≥0∞)
    (bound : ∀ (_reference : TranscriptOracle
      (programRecordHistory state.fixedTranscript (commandRecords values) ++ queries)),
      lower (((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
        (fun oracle => commands {state with fixedOracle := oracle.1} values)).toOuterMeasure
          {programmed | PermutationTranscriptMatches programmed.fixedOracle queries}) ≤ target) :
    lower (((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
      (fun oracle => commands {state with fixedOracle := oracle.1} values)).toOuterMeasure
        {programmed | PermutationTranscriptMatches programmed.fixedOracle queries}) ≤ target := by
  by_cases empty : ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
      (fun oracle => commands {state with fixedOracle := oracle.1} values)).toOuterMeasure
        {programmed | PermutationTranscriptMatches programmed.fixedOracle queries} = 0
  · rw [empty, atZero]
    exact bot_le
  · exact bound (Classical.choice (commands_extension_of_mass_ne_zero state values queries fresh empty))

end
end Kriterion.ArgoMAC.Shared.Simulator
