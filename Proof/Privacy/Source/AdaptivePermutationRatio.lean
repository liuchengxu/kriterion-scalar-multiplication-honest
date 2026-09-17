import Proof.Privacy.Collision.CircuitSlotRatio
import Proof.Privacy.Distribution.GateProgrammingDistribution

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography
open scoped ENNReal

noncomputable section

attribute [local instance] rawBucketUseFintype fixedQueryDomainFintype transcriptOracleFintype residualFixedQueryDomainFintype

/-- A uniform finite fiber has the exact conditional event mass. -/
theorem uniformSubtype_mass_mul {A : Type} [Fintype A] [Nonempty A]
    (kept event : A → Prop) [Fintype {a // kept a}] [Nonempty {a // kept a}] :
    (PMF.uniformOfFintype A).toOuterMeasure {a | kept a} *
      (PMF.uniformOfFintype {a // kept a}).toOuterMeasure {a | event a.1} =
        (PMF.uniformOfFintype A).toOuterMeasure {a | kept a ∧ event a} := by
  classical
  let intersection : ↑{a : {a // kept a} | event a.1} ≃ ↑{a : A | kept a ∧ event a} := {
    toFun a := ⟨a.1.1, a.1.2, a.2⟩
    invFun a := ⟨⟨a.1, a.2.1⟩, a.2.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  simp only [PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [show Fintype.card ↑{a : {a // kept a} | event a.1} =
    Fintype.card ↑{a : A | kept a ∧ event a} from Fintype.card_congr intersection]
  rw [show Fintype.card ↑{a : A | kept a} = Fintype.card {a // kept a} from
    Fintype.card_congr (Equiv.refl _)]
  simp only [div_eq_mul_inv]
  calc
    _ = (Fintype.card ↑{a : A | kept a ∧ event a} : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹ *
        ((Fintype.card {a // kept a} : ℝ≥0∞) * (Fintype.card {a // kept a} : ℝ≥0∞)⁻¹) := by ac_rfl
    _ = _ := by
      rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _), mul_one]

/-- This factor counts each distinct external domain once in its bucket. -/
def fixedTranscriptFactor [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block)) : ℝ≥0∞ :=
  ∏ index, ((Fintype.card Block - Fintype.card (FixedQueryDomain history index)).factorial : ℝ≥0∞) /
    (Fintype.card Block).factorial

/-- Every compatible fixed-oracle transcript has its exact finite-family mass. -/
theorem fixedTranscriptFactor_eq_mass [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (reference : PermutationOracle Pipeline.FixedKeyIndex Block)
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (compatible : PermutationTranscriptMatches reference history) :
    (PMF.uniformOfFintype (PermutationOracle Pipeline.FixedKeyIndex Block)).toOuterMeasure
      {oracle | PermutationTranscriptMatches oracle history} = fixedTranscriptFactor history := by
  let gates : Empty → RawGatePrescription := Empty.elim
  letI (index : Pipeline.FixedKeyIndex) : IsEmpty (RawBucketUse gates index) :=
    ⟨fun use => Empty.elim use.1.1⟩
  have domains (index) : Function.Injective (Sum.elim (rawBucketDomain gates index)
      (fun query : FixedQueryDomain history index => query.1)) := by
    intro first second equal
    rcases first with impossible | first
    · exact isEmptyElim impossible
    rcases second with impossible | second
    · exact isEmptyElim impossible
    exact congrArg Sum.inr (Subtype.ext equal)
  have ranges (index) : Function.Injective (Sum.elim (rawBucketRange gates index)
      (fun query : FixedQueryDomain history index => reference.permutation index query.1)) := by
    intro first second equal
    rcases first with impossible | first
    · exact isEmptyElim impossible
    rcases second with impossible | second
    · exact isEmptyElim impossible
    exact congrArg Sum.inr (Subtype.ext ((reference.permutation index).injective equal))
  have empty (index) : Fintype.card (RawBucketUse gates index) = 0 :=
    @Fintype.card_eq_zero _ _ ⟨fun use => Empty.elim use.1.1⟩
  have mass := rawFixedTranscript_mass gates reference history compatible domains ranges
  simpa only [empty, RawGarblingMatches, gates, IsEmpty.forall_iff, true_and,
    Nat.zero_add, fixedTranscriptFactor] using mass

/-- Transcript concatenation imposes both sets of recorded answers. -/
theorem permutationTranscriptMatches_append (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (first second : List (PermutationRecord Pipeline.FixedKeyIndex Block)) :
    PermutationTranscriptMatches oracle (first ++ second) ↔
      PermutationTranscriptMatches oracle first ∧ PermutationTranscriptMatches oracle second := by
  simp [PermutationTranscriptMatches, List.mem_append, or_imp, forall_and]

/-- The conditional uniform oracle fiber gives the exact extension mass, including replay queries. -/
theorem transcriptOracle_mass_mul [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (history queries : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (reference : TranscriptOracle (history ++ queries))
    [Nonempty (TranscriptOracle history)] :
    fixedTranscriptFactor history *
      (PMF.uniformOfFintype (TranscriptOracle history)).toOuterMeasure
        {oracle | PermutationTranscriptMatches oracle.1 queries} =
      fixedTranscriptFactor (history ++ queries) := by
  classical
  let compatible := (permutationTranscriptMatches_append reference.1 history queries).mp reference.2
  rw [← fixedTranscriptFactor_eq_mass reference.1 history compatible.1]
  have mass := @uniformSubtype_mass_mul (PermutationOracle Pipeline.FixedKeyIndex Block)
    inferInstance inferInstance (PermutationTranscriptMatches · history)
    (PermutationTranscriptMatches · queries) (transcriptOracleFintype history) ⟨⟨reference.1, compatible.1⟩⟩
  exact mass.trans (by
    rw [show {oracle : PermutationOracle Pipeline.FixedKeyIndex Block |
      PermutationTranscriptMatches oracle history ∧ PermutationTranscriptMatches oracle queries} =
      {oracle | PermutationTranscriptMatches oracle (history ++ queries)} by
      ext oracle
      exact (permutationTranscriptMatches_append oracle history queries).symm]
    exact fixedTranscriptFactor_eq_mass reference.1 _ reference.2)


/-- The record history retains exactly the old records and the programmed records. -/
theorem mem_programRecordHistory_iff
    (history records : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (record : PermutationRecord Pipeline.FixedKeyIndex Block) :
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
    (records : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (index : Pipeline.FixedKeyIndex) : Set Block :=
  {domain | ∃ record ∈ records, record.index = index ∧ record.domain = domain}

/-- The extended domain count splits programmed domains from all residual queries. -/
def programmedQueryDomainEquiv
    (history records queries : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (index : Pipeline.FixedKeyIndex) :
    FixedQueryDomain (programRecordHistory history records ++ queries) index ≃
      FixedQueryDomain records index ⊕
        ResidualFixedQueryDomain (history ++ queries) (programmedDomains records) index := by
  classical
  let join : FixedQueryDomain records index ⊕
      ResidualFixedQueryDomain (history ++ queries) (programmedDomains records) index →
      FixedQueryDomain (programRecordHistory history records ++ queries) index := fun query =>
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
    (history records queries : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (index : Pipeline.FixedKeyIndex) :
    Fintype.card (FixedQueryDomain (programRecordHistory history records ++ queries) index) =
      Fintype.card (FixedQueryDomain records index) +
        Fintype.card (ResidualFixedQueryDomain (history ++ queries) (programmedDomains records) index) := by
  classical
  exact (Fintype.card_congr (programmedQueryDomainEquiv history records queries index)).trans
    Fintype.card_sum


/-- Every fresh program avoids every earlier external query. -/
theorem freshRecordSchedule_againstHistory
    (history records : List (PermutationRecord Pipeline.FixedKeyIndex Block))
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
    (history records : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule history records) (index : Pipeline.FixedKeyIndex) :
    ResidualFixedQueryDomain history (programmedDomains records) index ≃ FixedQueryDomain history index where
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
    (history records : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule history records) (index : Pipeline.FixedKeyIndex) :
    Fintype.card (FixedQueryDomain (programRecordHistory history records) index) =
      Fintype.card (FixedQueryDomain records index) + Fintype.card (FixedQueryDomain history index) := by
  have count := programmedQueryDomain_card history records [] index
  simp only [List.append_nil] at count
  exact count.trans (congrArg (Fintype.card (FixedQueryDomain records index) + ·)
    (Fintype.card_congr (freshProgrammedResidualEquiv history records fresh index)))

/-- A finite transcript factor is positive. -/
theorem fixedTranscriptFactor_ne_zero [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block)) : fixedTranscriptFactor history ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro index _
  exact ENNReal.div_ne_zero.mpr ⟨Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _),
    ENNReal.natCast_ne_top _⟩

/-- A finite transcript factor is finite. -/
theorem fixedTranscriptFactor_ne_top [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block)) : fixedTranscriptFactor history ≠ ⊤ := by
  classical
  exact ENNReal.prod_ne_top fun index _ => ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))


/-- The extended oracle factor uses programmed domains plus residual external domains. -/
theorem programmedTranscriptFactor_eq [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (history records queries : List (PermutationRecord Pipeline.FixedKeyIndex Block)) :
    fixedTranscriptFactor (programRecordHistory history records ++ queries) =
      ∏ index, ((Fintype.card Block - (Fintype.card (FixedQueryDomain records index) +
        Fintype.card (ResidualFixedQueryDomain (history ++ queries)
          (programmedDomains records) index))).factorial : ℝ≥0∞) / (Fintype.card Block).factorial := by
  unfold fixedTranscriptFactor
  apply Finset.prod_congr rfl
  intro index _
  rw [programmedQueryDomain_card]

/-- Fresh programming uses the earlier query count in its denominator. -/
theorem freshProgrammedTranscriptFactor_eq [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (history records : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule history records) :
    fixedTranscriptFactor (programRecordHistory history records) =
      ∏ index, ((Fintype.card Block - (Fintype.card (FixedQueryDomain records index) +
        Fintype.card (FixedQueryDomain history index))).factorial : ℝ≥0∞) /
          (Fintype.card Block).factorial := by
  unfold fixedTranscriptFactor
  apply Finset.prod_congr rfl
  intro index _
  rw [freshProgrammedQueryDomain_card history records fresh]

attribute [local irreducible] PMF.uniformOfFintype PMF.map PMF.toOuterMeasure fixedTranscriptFactor

/-- An arbitrary observation preserves the exact conditional transcript mass. -/
theorem transcriptOracle_map_mass_mul [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (history queries : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (reference : TranscriptOracle (history ++ queries)) [Nonempty (TranscriptOracle history)]
    {State : Type} (embed : TranscriptOracle history → State) (event : Set State)
    (projection : ∀ oracle, embed oracle ∈ event ↔ PermutationTranscriptMatches oracle.1 queries) :
    fixedTranscriptFactor history *
      ((PMF.uniformOfFintype (TranscriptOracle history)).map embed).toOuterMeasure event =
      fixedTranscriptFactor (history ++ queries) := by
  rw [PMF.toOuterMeasure_map_apply]
  have eventEqual : embed ⁻¹' event = {oracle | PermutationTranscriptMatches oracle.1 queries} := by
    ext oracle
    exact projection oracle
  rw [eventEqual]
  exact transcriptOracle_mass_mul history queries reference

/-- Exact fresh transcript programming gives the conditional post-query mass. -/
theorem programTranscriptRecords_queryMass_mul [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (history records queries : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule history records) [Nonempty (TranscriptOracle history)]
    (reference : TranscriptOracle (programRecordHistory history records ++ queries)) :
    fixedTranscriptFactor (programRecordHistory history records) *
      ((PMF.uniformOfFintype (TranscriptOracle history)).map
        (programTranscriptRecords history records fresh)).toOuterMeasure
          {oracle | PermutationTranscriptMatches oracle.1 queries} =
      fixedTranscriptFactor (programRecordHistory history records ++ queries) := by
  letI : Nonempty (TranscriptOracle (programRecordHistory history records)) :=
    ⟨programTranscriptRecords history records fresh (Classical.arbitrary _)⟩
  rw [programTranscriptRecords_uniform history records fresh]
  exact transcriptOracle_mass_mul (programRecordHistory history records) queries reference


/-- The actual record schedule has this exact conditional post-query density. -/
theorem programTranscriptRecords_queryMass [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (history records queries : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule history records) [Nonempty (TranscriptOracle history)]
    (reference : TranscriptOracle (programRecordHistory history records ++ queries)) :
    ((PMF.uniformOfFintype (TranscriptOracle history)).map
      (programTranscriptRecords history records fresh)).toOuterMeasure
        {oracle | PermutationTranscriptMatches oracle.1 queries} =
      fixedTranscriptFactor (programRecordHistory history records ++ queries) /
        fixedTranscriptFactor (programRecordHistory history records) := by
  apply (ENNReal.eq_div_iff (fixedTranscriptFactor_ne_zero _) (fixedTranscriptFactor_ne_top _)).mpr
  exact programTranscriptRecords_queryMass_mul history records queries fresh reference


/-- The exact programmed density retains every post-encode replay query. -/
theorem programTranscriptRecords_queryMass_product [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (history records queries : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule history records) [Nonempty (TranscriptOracle history)]
    (reference : TranscriptOracle (programRecordHistory history records ++ queries)) :
    ((PMF.uniformOfFintype (TranscriptOracle history)).map
      (programTranscriptRecords history records fresh)).toOuterMeasure
        {oracle | PermutationTranscriptMatches oracle.1 queries} =
      (∏ index, ((Fintype.card Block - (Fintype.card (FixedQueryDomain records index) +
        Fintype.card (ResidualFixedQueryDomain (history ++ queries)
          (programmedDomains records) index))).factorial : ℝ≥0∞) / (Fintype.card Block).factorial) /
      (∏ index, ((Fintype.card Block - (Fintype.card (FixedQueryDomain records index) +
        Fintype.card (FixedQueryDomain history index))).factorial : ℝ≥0∞) /
          (Fintype.card Block).factorial) := by
  rw [programTranscriptRecords_queryMass history records queries fresh reference,
    programmedTranscriptFactor_eq, freshProgrammedTranscriptFactor_eq history records fresh]

/-- The recording ideal handler gives the same answers as the real oracle family. -/
theorem idealOracleTranscriptCompatible_iff_real (state : SimulatorState) (reference : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (fixed : state.fixedOracle = reference.fixedKeyOracle)
    (enc : state.encOracle = reference.encPRFOracle) (hash : state.hashOracle = reference.hashOracle) :
    OracleTranscriptCompatible idealOracleHandler state transcript ↔
      OracleTranscriptCompatible Garbling.oracleHandler reference transcript := by
  induction transcript generalizing state with
  | nil => rfl
  | cons entry remaining inductionHypothesis =>
      rcases entry with ⟨request, answer⟩
      cases request <;>
        simp only [OracleTranscriptCompatible, idealOracleHandler, oracleHandlerFor, Garbling.oracleHandler, Cryptography.publicHandler, Cryptography.publicAnswer]
      all_goals
        apply and_congr
        · simp only [fixed, enc, hash] <;> rfl
        · exact inductionHypothesis _ fixed enc hash

/-- This active-slot factor uses the actual query count before encoding. -/
def activeIdealSlotFactor (N Q prior residual : Nat) : ℝ≥0∞ :=
  ((N : ℝ≥0∞) ^ Q)⁻¹ * ((N - prior).factorial : ℝ≥0∞) / N.factorial *
    ((N - (Q + residual)).factorial : ℝ≥0∞) / (N - (Q + prior)).factorial

/-- Active programming cancels its conditional denominator exactly. -/
theorem activeIdealSlotFactor_eq (N Q prior residual : Nat) (fits : Q + prior ≤ N) :
    activeIdealSlotFactor N Q prior residual =
      ((N - prior).descFactorial Q : ℝ≥0∞) * ((N : ℝ≥0∞) ^ Q)⁻¹ *
        ((N - (Q + residual)).factorial : ℝ≥0∞) / N.factorial := by
  have factorial : (N - prior).factorial =
      (N - (Q + prior)).factorial * (N - prior).descFactorial Q := by
    have equal := (Nat.factorial_mul_descFactorial (by omega : Q ≤ N - prior)).symm
    simpa only [Nat.sub_sub, Nat.add_comm prior Q] using equal
  unfold activeIdealSlotFactor
  rw [factorial, Nat.cast_mul]
  simp only [div_eq_mul_inv]
  calc
    _ = (((N - prior).descFactorial Q : ℝ≥0∞) * ((N : ℝ≥0∞) ^ Q)⁻¹ *
        ((N - (Q + residual)).factorial : ℝ≥0∞) * (N.factorial : ℝ≥0∞)⁻¹) *
        (((N - (Q + prior)).factorial : ℝ≥0∞) *
          ((N - (Q + prior)).factorial : ℝ≥0∞)⁻¹) := by ring
    _ = _ := by
      rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
        (ENNReal.natCast_ne_top _), mul_one]

/-- The exact active simulator factor never exceeds the real permutation factor. -/
theorem activeIdealSlotFactor_le (N Q prior residual : Nat) (positive : 0 < N)
    (fits : Q + prior ≤ N) :
    activeIdealSlotFactor N Q prior residual ≤
      ((N - (Q + residual)).factorial : ℝ≥0∞) / N.factorial := by
  rw [activeIdealSlotFactor_eq N Q prior residual fits]
  have count : ((N - prior).descFactorial Q : ℝ≥0∞) ≤ (N : ℝ≥0∞) ^ Q := by
    exact_mod_cast (Nat.descFactorial_le_pow (N - prior) Q).trans
      (Nat.pow_le_pow_left (Nat.sub_le N prior) Q)
  have ratio : ((N - prior).descFactorial Q : ℝ≥0∞) * ((N : ℝ≥0∞) ^ Q)⁻¹ ≤ 1 := by
    apply (mul_le_mul_left count _).trans
    rw [ENNReal.mul_inv_cancel
      (ENNReal.pow_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt positive)) _)
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))]
  have bound := mul_le_mul_left ratio
    (((N - (Q + residual)).factorial : ℝ≥0∞) / N.factorial)
  simpa only [one_mul, ← mul_div_assoc] using bound

/-- This factor keeps active and inactive slots in one exact transcript product. -/
def adaptiveIdealPermutationFactor {Index : Type} [Fintype Index]
    (N : Nat) (uses prior residual : Index → Nat) (active : Index → Bool) : ℝ≥0∞ :=
  ∏ index, if active index then activeIdealSlotFactor N (uses index) (prior index) (residual index)
    else ((N : ℝ≥0∞) ^ uses index)⁻¹ *
      ((N - residual index).factorial : ℝ≥0∞) / N.factorial

/-- The exact active factors and independent inactive factors fit the real product. -/
theorem adaptiveIdealPermutationFactor_le {Index : Type} [Fintype Index]
    (N : Nat) (uses prior residual : Index → Nat) (active : Index → Bool) (positive : 0 < N)
    (priorFits : ∀ index, uses index + prior index ≤ N)
    (residualFits : ∀ index, uses index + residual index ≤ N) :
    adaptiveIdealPermutationFactor N uses prior residual active ≤
      ∏ index, ((N - (uses index + residual index)).factorial : ℝ≥0∞) / N.factorial := by
  classical
  apply Finset.prod_le_prod'
  intro index _
  cases selected : active index
  · exact factorial_ratio_ge_inverse_power N (uses index) (residual index) positive (residualFits index)
  · exact activeIdealSlotFactor_le N (uses index) (prior index) (residual index) positive (priorFits index)


/-- The corrected adaptive factor fits the concrete real transcript mass. -/
theorem circuitSharedInactive_adaptiveFactor_mass_ge
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (selected : RawLabelBucket → Bool) (wire : RawLabelBucket → Wire) (shift : RawLabelBucket → Block)
    (publicLabel : RawLabelBucket → Block) (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript)
    (offsetsDistinct : ∀ index, Function.Injective
      (rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index))
    (referenceActive : ∀ index, rawSlotBranch index.slot = selected (rawLabelBucket index) →
      ∀ use : RawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index,
        randomness.fixedKeyOracle.permutation index
          (publicLabel (rawLabelBucket index) ^^^
            rawBucketTweak (circuitRawGatePrescription keys slopes lifts tables) index use) =
          rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index use ^^^
            publicLabel (rawLabelBucket index))
    (prior : Pipeline.FixedKeyIndex → Nat)
    (priorFits : ∀ index, circuitBucketSize index + prior index ≤ Fintype.card Block)
    (residualFits : ∀ index, circuitBucketSize index + circuitResidualQueryCount
      (circuitRawGatePrescription keys slopes lifts tables) selected publicLabel transcript index ≤
        Fintype.card Block) :
    (1 - (182 * transcript.length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      adaptiveIdealPermutationFactor (Fintype.card Block) circuitBucketSize prior
        (circuitResidualQueryCount (circuitRawGatePrescription keys slopes lifts tables)
          selected publicLabel transcript)
        (fun index => decide (rawSlotBranch index.slot = selected (rawLabelBucket index))) ≤
    (PMF.uniformOfFintype
      ((PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block))).toOuterMeasure
        {sample | RawGarblingMatches
          (rawGatesWithLabels (circuitRawGatePrescription keys slopes lifts tables)
            (rawMixedLabels selected publicLabel wire shift sample.2)) sample.1 ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with fixedKeyOracle := sample.1} transcript} := by
  apply le_trans _ (circuitSharedInactive_realTranscript_mass_ge keys slopes lifts tables selected
    wire shift publicLabel randomness transcript compatible offsetsDistinct referenceActive)
  exact mul_le_mul_right (adaptiveIdealPermutationFactor_le _ _ _ _ _ Fintype.card_pos
    priorFits residualFits) _

end
end Kriterion.ArgoMAC.Security
