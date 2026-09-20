import Proof.Privacy.Source.SharedQueryCounts

namespace Kriterion.ArgoMAC.Shared.Simulator
open BN254 Cryptography Security SharedQueryCounts
open scoped ENNReal
noncomputable section
set_option maxRecDepth 2048
attribute [local instance] transcriptOracleFintype

/-- A compatible transcript has positive mass in the shared oracle. -/
theorem transcriptMass_ne_zero [Fintype Block]
    (history : List (PermutationRecord FixedKeyIndex Block))
    (reference : TranscriptOracle history) : transcriptMass history ≠ 0 := by
  rw [sharedTranscriptMass_eq_product reference.1 history reference.2]
  apply Finset.prod_ne_zero_iff.mpr
  intro index _
  exact ENNReal.div_ne_zero.mpr ⟨Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _),
    ENNReal.natCast_ne_top _⟩

/-- A compatible transcript has finite mass in the shared oracle. -/
theorem transcriptMass_ne_top [Fintype Block]
    (history : List (PermutationRecord FixedKeyIndex Block))
    (reference : TranscriptOracle history) : transcriptMass history ≠ ⊤ := by
  rw [sharedTranscriptMass_eq_product reference.1 history reference.2]
  exact ENNReal.prod_ne_top fun index _ => ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- The actual shared command interpreter gives this exact conditional query mass. -/
theorem commands_queryMass [Fintype Block] (state : OracleState) (values : List FixedCommand)
    (queries : List (PermutationRecord FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript (commandRecords values))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (reference : TranscriptOracle (programRecordHistory state.fixedTranscript (commandRecords values))) :
    ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
      (fun oracle => commands {state with fixedOracle := oracle.1} values)).toOuterMeasure
      {next | PermutationTranscriptMatches next.fixedOracle queries} =
    transcriptMass (programRecordHistory state.fixedTranscript (commandRecords values) ++ queries) /
      transcriptMass (programRecordHistory state.fixedTranscript (commandRecords values)) := by
  apply (ENNReal.eq_div_iff (transcriptMass_ne_zero _ reference) (transcriptMass_ne_top _ reference)).mpr
  exact commands_queryMass_mul state values queries fresh

/-- The shared query factor counts active domains and residual domains in the same slot. -/
theorem commands_queryMass_product [Fintype Block] (state : OracleState) (values : List FixedCommand)
    (queries : List (PermutationRecord FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript (commandRecords values))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (reference : TranscriptOracle
      (programRecordHistory state.fixedTranscript (commandRecords values) ++ queries)) :
    ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
      (fun oracle => commands {state with fixedOracle := oracle.1} values)).toOuterMeasure
      {next | PermutationTranscriptMatches next.fixedOracle queries} =
      (∏ index : FixedKeyIndex,
        ((Fintype.card Block - (Fintype.card (SharedQueryDomain (commandRecords values) index) +
          Fintype.card (ResidualQueryDomain (state.fixedTranscript ++ queries)
            (programmedDomains (commandRecords values)) index))).factorial : ENNReal) /
              (Fintype.card Block).factorial) /
      (∏ index : FixedKeyIndex,
        ((Fintype.card Block - (Fintype.card (SharedQueryDomain (commandRecords values) index) +
          Fintype.card (SharedQueryDomain state.fixedTranscript index))).factorial : ENNReal) /
            (Fintype.card Block).factorial) := by
  have before : PermutationTranscriptMatches reference.1
      (programRecordHistory state.fixedTranscript (commandRecords values)) := by
    intro record member
    exact reference.2 record (List.mem_append_left queries member)
  rw [commands_queryMass state values queries fresh ⟨reference.1, before⟩,
    sharedTranscriptMass_eq_product reference.1 _ reference.2,
    sharedTranscriptMass_eq_product reference.1 _ before]
  apply congrArg₂ (fun numerator denominator : ENNReal => numerator / denominator)
  · apply Finset.prod_congr rfl
    intro index _
    rw [SharedQueryCounts.programmedQueryDomain_card]
  · apply Finset.prod_congr rfl
    intro index _
    rw [SharedQueryCounts.freshProgrammedQueryDomain_card _ _ fresh]

end
end Kriterion.ArgoMAC.Shared.Simulator
