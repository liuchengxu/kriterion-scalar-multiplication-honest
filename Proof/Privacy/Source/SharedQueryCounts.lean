import Proof.Privacy.Source.SharedTranscriptMass

namespace Kriterion.ArgoMAC.Security.SharedQueryCounts
open BN254 Cryptography
noncomputable section

/-- A residual query has a domain outside the programmed domain set. -/
def ResidualQueryDomain
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (covered : Shared.FixedKeyIndex → Set Block) (index : Shared.FixedKeyIndex) :=
  {query : SharedQueryDomain history index // query.1 ∉ covered index}

instance residualQueryDomainFintype [Fintype Block]
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (covered : Shared.FixedKeyIndex → Set Block) (index : Shared.FixedKeyIndex) :
    Fintype (ResidualQueryDomain history covered index) := by
  classical
  unfold ResidualQueryDomain
  infer_instance

/-- The record history retains exactly the old records and the programmed records. -/
theorem mem_programRecordHistory_iff
    (history records : List (PermutationRecord Shared.FixedKeyIndex Block))
    (record : PermutationRecord Shared.FixedKeyIndex Block) :
    record ∈ programRecordHistory history records ↔ record ∈ records ∨ record ∈ history := by
  induction records generalizing history with
  | nil => simp [programRecordHistory]
  | cons current rest inductionHypothesis =>
      change record ∈ programRecordHistory (current :: history) rest ↔ _
      rw [inductionHypothesis]
      simp only [List.mem_cons]
      tauto

/-- The programmed domain set counts repeated queries only once. -/
def programmedDomains
    (records : List (PermutationRecord Shared.FixedKeyIndex Block))
    (index : Shared.FixedKeyIndex) : Set Block :=
  {domain | ∃ record ∈ records, record.index = index ∧ record.domain = domain}

/-- The extended domain count splits programmed domains from all residual queries. -/
def programmedQueryDomainEquiv
    (history records queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    (index : Shared.FixedKeyIndex) :
    SharedQueryDomain (programRecordHistory history records ++ queries) index ≃
      SharedQueryDomain records index ⊕
        ResidualQueryDomain (history ++ queries) (programmedDomains records) index := by
  classical
  let join : SharedQueryDomain records index ⊕
      ResidualQueryDomain (history ++ queries) (programmedDomains records) index →
      SharedQueryDomain (programRecordHistory history records ++ queries) index := fun query =>
    match query with
    | .inl query => ⟨query.1, by
        obtain ⟨record, member, equal⟩ := query.2
        exact ⟨record, List.mem_append_left _ ((mem_programRecordHistory_iff _ _ _).mpr
          (Or.inl member)), equal⟩⟩
    | .inr query => ⟨query.1.1, by
        obtain ⟨record, member, equal⟩ := query.1.2
        refine ⟨record, ?_, equal⟩
        rcases List.mem_append.mp member with old | later
        · exact List.mem_append_left _ ((mem_programRecordHistory_iff _ _ _).mpr (Or.inr old))
        · exact List.mem_append_right _ later⟩
  apply (Equiv.ofBijective join ?_).symm
  constructor
  · intro first second equal
    have values := congrArg Subtype.val equal
    cases first with
    | inl first =>
        cases second with
        | inl second => exact congrArg Sum.inl (Subtype.ext values)
        | inr second =>
            exact False.elim (second.2 (values ▸ first.2))
    | inr first =>
        cases second with
        | inl second => exact False.elim (first.2 (values.symm ▸ second.2))
        | inr second => exact congrArg Sum.inr (Subtype.ext (Subtype.ext values))
  · intro query
    by_cases programmed : query.1 ∈ programmedDomains records index
    · exact ⟨Sum.inl ⟨query.1, programmed⟩, rfl⟩
    · refine ⟨Sum.inr ⟨⟨query.1, ?_⟩, programmed⟩, rfl⟩
      obtain ⟨record, member, equal⟩ := query.2
      refine ⟨record, ?_, equal⟩
      rcases List.mem_append.mp member with before | later
      · rcases (mem_programRecordHistory_iff _ _ _).mp before with assigned | old
        · exact False.elim (programmed ⟨record, assigned, equal⟩)
        · exact List.mem_append_left _ old
      · exact List.mem_append_right _ later

/-- This exact count permits queries that replay programmed assignments. -/
theorem programmedQueryDomain_card [Fintype Block]
    (history records queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    (index : Shared.FixedKeyIndex) :
    Fintype.card (SharedQueryDomain (programRecordHistory history records ++ queries) index) =
      Fintype.card (SharedQueryDomain records index) +
        Fintype.card (ResidualQueryDomain (history ++ queries) (programmedDomains records) index) := by
  classical
  exact (Fintype.card_congr (programmedQueryDomainEquiv history records queries index)).trans
    Fintype.card_sum


/-- Every fresh program avoids every earlier external query. -/
theorem freshRecordSchedule_againstHistory
    (history records : List (PermutationRecord Shared.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule history records) :
    ∀ record ∈ records, FreshPermutationPair history record.index record.domain record.range := by
  induction records generalizing history with
  | nil => simp
  | cons current rest inductionHypothesis =>
      intro record member prior priorMember sameIndex
      rcases List.mem_cons.mp member with equal | later
      · subst record
        exact fresh.1 prior priorMember sameIndex
      · exact inductionHypothesis (current :: history) fresh.2 record later prior
          (List.mem_cons_of_mem _ priorMember) sameIndex

/-- Fresh programs remove no domain from the earlier query transcript. -/
def freshProgrammedResidualEquiv
    (history records : List (PermutationRecord Shared.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule history records) (index : Shared.FixedKeyIndex) :
    ResidualQueryDomain history (programmedDomains records) index ≃ SharedQueryDomain history index where
  toFun query := query.1
  invFun query := ⟨query, by
    intro assigned
    obtain ⟨record, member, sameIndex, sameDomain⟩ := assigned
    obtain ⟨prior, priorMember, priorIndex, priorDomain⟩ := query.2
    exact (freshRecordSchedule_againstHistory history records fresh record member prior priorMember
      (priorIndex.trans sameIndex.symm)).1 (priorDomain.trans sameDomain.symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Fresh programs add their distinct domains to the earlier query count. -/
theorem freshProgrammedQueryDomain_card [Fintype Block]
    (history records : List (PermutationRecord Shared.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule history records) (index : Shared.FixedKeyIndex) :
    Fintype.card (SharedQueryDomain (programRecordHistory history records) index) =
      Fintype.card (SharedQueryDomain records index) + Fintype.card (SharedQueryDomain history index) := by
  have count := programmedQueryDomain_card history records [] index
  simp only [List.append_nil] at count
  exact count.trans (congrArg (Fintype.card (SharedQueryDomain records index) + ·)
    (Fintype.card_congr (freshProgrammedResidualEquiv history records fresh index)))

end
end Kriterion.ArgoMAC.Security.SharedQueryCounts
