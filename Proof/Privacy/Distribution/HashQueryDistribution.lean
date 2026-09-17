import Proof.Privacy.Transcript.OracleTranscript
import Construction.Garbling
import Proof.Privacy.Distribution.Distribution

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section


/-- This update changes only the hash answer at one field input. -/
def replaceHashAt (randomness : Garbling.Randomness) (hidden : BaseField)
    (answer : Block × Block) : Garbling.Randomness :=
  { randomness with hashOracle := Function.update randomness.hashOracle hidden answer }

/-- This list contains the hash inputs in a public oracle transcript. -/
def transcriptHashInputs (transcript : List (Sigma Garbling.oracleSpec.Answer)) : List BaseField :=
  transcript.filterMap fun entry => match entry.1 with
    | .hash input => some input
    | _ => none

/-- A hidden hash input does not change another oracle answer. -/
theorem replaceHashAt_answer (randomness : Garbling.Randomness) (hidden : BaseField)
    (answer : Block × Block) (request : Garbling.OracleQuery)
    (miss : request ≠ .hash hidden) :
    (Garbling.oracleHandler request (replaceHashAt randomness hidden answer)).1 =
      (Garbling.oracleHandler request randomness).1 := by
  cases request <;> try rfl
  rename_i input
  change Function.update randomness.hashOracle hidden answer input = randomness.hashOracle input
  exact Function.update_of_ne (fun same => miss (congrArg Cryptography.PublicQuery.hash same)) _ _

theorem oracleHandler_state (randomness : Garbling.Randomness)
    (request : Garbling.OracleQuery) :
    (Garbling.oracleHandler request randomness).2 = randomness := by
  cases request <;> rfl

/-- Both hash tapes have the same compatibility predicate until the hidden input occurs. -/
theorem replaceHashAt_compatible (randomness : Garbling.Randomness) (hidden : BaseField)
    (answer : Block × Block) (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (miss : hidden ∉ transcriptHashInputs transcript) :
    OracleTranscriptCompatible Garbling.oracleHandler
        (replaceHashAt randomness hidden answer) transcript ↔
      OracleTranscriptCompatible Garbling.oracleHandler randomness transcript := by
  induction transcript with
  | nil => rfl
  | cons entry tail ih =>
      have tailMiss : hidden ∉ transcriptHashInputs tail := by
        intro member
        apply miss
        cases entry with
        | mk request value => cases request <;> simp_all [transcriptHashInputs]
      have queryMiss : entry.1 ≠ .hash hidden := by
        intro equal
        apply miss
        simp [transcriptHashInputs, equal]
      simp only [OracleTranscriptCompatible,
        oracleHandler_state (replaceHashAt randomness hidden answer) entry.1,
        oracleHandler_state randomness entry.1,
        replaceHashAt_answer randomness hidden answer entry.1 queryMiss, ih tailMiss]

/-- Every good public transcript has exactly the same mass after the hash update. -/
theorem replaceHashAt_transcript_mass {Result : Type*} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget)
    (randomness : Garbling.Randomness) (hidden : BaseField) (answer : Block × Block)
    (result : Result) (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (miss : hidden ∉ transcriptHashInputs transcript) :
    ((runOracleProgramWithTranscript Garbling.oracleHandler program
      (replaceHashAt randomness hidden answer)).map (fun output => (output.1, output.2.2)))
        (result, transcript) =
    ((runOracleProgramWithTranscript Garbling.oracleHandler program randomness).map
      (fun output => (output.1, output.2.2))) (result, transcript) := by
  by_cases compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript
  · exact runOracleProgramWithTranscript_mass_eq _ _ _ _ _ _ _
      ((replaceHashAt_compatible randomness hidden answer transcript miss).mpr compatible) compatible
  · rw [runOracleProgramWithTranscript_mass_zero _ _ _ _ _ compatible,
      runOracleProgramWithTranscript_mass_zero]
    exact fun other => compatible
      ((replaceHashAt_compatible randomness hidden answer transcript miss).mp other)

/-- The public transcript cannot exceed the program query budget. -/
theorem runOracleProgramWithTranscript_length_le
    {oracle : OracleSpec} {Result State : Type*} (handler : OracleHandler oracle State)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State)
    (output : Result × State × List (Sigma oracle.Answer))
    (member : output ∈ (runOracleProgramWithTranscript handler program state).support) :
    output.2.2.length ≤ budget := by
  induction program generalizing state output with
  | pure result =>
      simp only [runOracleProgramWithTranscript_pure, PMF.mem_support_map_iff] at member
      obtain ⟨value, _, rfl⟩ := member
      exact Nat.zero_le _
  | query request next ih =>
      simp only [runOracleProgramWithTranscript_query, PMF.mem_support_map_iff] at member
      obtain ⟨tail, tailMember, rfl⟩ := member
      exact Nat.add_le_add_right (ih _ _ tail tailMember) 1
  | sample distribution next ih =>
      simp only [runOracleProgramWithTranscript_sample, PMF.mem_support_bind_iff] at member
      obtain ⟨value, _, tailMember⟩ := member
      exact ih value state output tailMember

variable [Fintype BaseField]

/-- A fixed transcript hits a uniform field input with probability at most its length over p. -/
theorem uniform_hidden_transcript_hit (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (PMF.uniformOfFintype BaseField).toOuterMeasure
      {hidden | hidden ∈ transcriptHashInputs transcript} ≤
      (transcript.length : ENNReal) / baseFieldModulus := by
  classical
  have event : {hidden | hidden ∈ transcriptHashInputs transcript} =
      (transcriptHashInputs transcript).toFinset := by ext; simp
  rw [event, PMF.toOuterMeasure_uniformOfFintype_apply,
    Fintype.card_of_subtype (transcriptHashInputs transcript).toFinset (by simp)]
  have size : (transcriptHashInputs transcript).toFinset.card ≤ transcript.length :=
    (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)
  simpa using
    ENNReal.div_le_div_right (show ((transcriptHashInputs transcript).toFinset.card : ENNReal) ≤
      transcript.length from by exact_mod_cast size) (baseFieldModulus : ENNReal)

/-- This PMF erases the private oracle state from a program run. -/
def hashTranscriptRun {Result : Type*} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget)
    (randomness : Garbling.Randomness) :=
  (runOracleProgramWithTranscript Garbling.oracleHandler program randomness).map
    (fun output => (output.1, output.2.2))

omit [Fintype BaseField] in
theorem hashTranscriptRun_length_le {Result : Type*} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget)
    (randomness : Garbling.Randomness)
    (output : Result × List (Sigma Garbling.oracleSpec.Answer))
    (member : output ∈ (hashTranscriptRun program randomness).support) :
    output.2.length ≤ budget := by
  simp only [hashTranscriptRun, PMF.mem_support_map_iff] at member
  obtain ⟨value, valueMember, rfl⟩ := member
  exact runOracleProgramWithTranscript_length_le _ _ _ _ valueMember

/-- This PMF retains the hidden input to define its query-hit event. -/
def withUniformHidden {Output : Type*} (runs : BaseField → PMF Output) :
    PMF (BaseField × Output) :=
  (PMF.uniformOfFintype BaseField).bind fun hidden =>
    (runs hidden).map (Prod.mk hidden)

omit [Fintype BaseField] in
theorem bind_pair_apply {Input Output : Type*} (inputs : PMF Input)
    (runs : Input → PMF Output) (input : Input) (output : Output) :
    (inputs.bind fun value => (runs value).map (Prod.mk value)) (input, output) =
      inputs input * runs input output := by
  classical
  rw [PMF.bind_apply, tsum_eq_single input]
  · congr 1
    rw [PMF.map_apply, tsum_eq_single output]
    · simp
    · intro other different
      simp [Ne.symm different]
  · intro other different
    simp [PMF.map_apply, Ne.symm different]

theorem withUniformHidden_apply {Output : Type*} (runs : BaseField → PMF Output)
    (hidden : BaseField) (output : Output) :
    withUniformHidden runs (hidden, output) =
      (PMF.uniformOfFintype BaseField) hidden * runs hidden output := by
  exact bind_pair_apply (PMF.uniformOfFintype BaseField) runs hidden output

/-- An independent hidden input meets any bounded adaptive transcript with probability at most q/p. -/
theorem uniform_hidden_query_hit_bound {Result : Type*}
    (transcripts : PMF (Result × List (Sigma Garbling.oracleSpec.Answer)))
    (budget : Nat) (lengthBound : ∀ output ∈ transcripts.support, output.2.length ≤ budget) :
    (withUniformHidden (fun _ => transcripts)).toOuterMeasure
      {output | output.1 ∈ transcriptHashInputs output.2.2} ≤
      (budget : ENNReal) / baseFieldModulus := by
  have swap : withUniformHidden (fun _ => transcripts) = transcripts.bind fun output =>
      (PMF.uniformOfFintype BaseField).map (fun hidden => (hidden, output)) :=
    PMF.bind_comm _ _ (fun hidden output => PMF.pure (hidden, output))
  rw [swap]
  apply Probability.bind_event_le
  intro output member
  rw [PMF.toOuterMeasure_map_apply]
  exact (uniform_hidden_transcript_hit output.2).trans
    (ENNReal.div_le_div_right (by exact_mod_cast lengthBound output member) _)

/-- An arbitrary hash replacement costs at most q/p for a program with a hidden uniform input. -/
theorem replaceHashAt_event_bound {Result : Type*} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget)
    (randomness : Garbling.Randomness) (answers : BaseField → Block × Block)
    (event : Set (BaseField × Result × List (Sigma Garbling.oracleSpec.Answer))) :
    |((withUniformHidden (fun hidden => hashTranscriptRun program
        (replaceHashAt randomness hidden (answers hidden)))).toOuterMeasure event).toReal -
      ((withUniformHidden (fun _ => hashTranscriptRun program randomness)).toOuterMeasure event).toReal| ≤ (budget : ℝ) / baseFieldModulus := by
  let real := withUniformHidden fun hidden => hashTranscriptRun program
    (replaceHashAt randomness hidden (answers hidden))
  let ideal := withUniformHidden fun _ => hashTranscriptRun program randomness
  let bad : Set (BaseField × Result × List (Sigma Garbling.oracleSpec.Answer)) :=
    {output | output.1 ∈ transcriptHashInputs output.2.2}
  have hit := uniform_hidden_query_hit_bound (hashTranscriptRun program randomness) budget
    (hashTranscriptRun_length_le program randomness)
  have bound := Probability.identical_until_bad real ideal bad event (by
    rintro ⟨hidden, result, transcript⟩ miss
    change withUniformHidden _ (hidden, result, transcript) = withUniformHidden _ (hidden, result, transcript)
    rw [withUniformHidden_apply, withUniformHidden_apply]
    exact congrArg ((PMF.uniformOfFintype BaseField) hidden * ·)
      (replaceHashAt_transcript_mass program randomness hidden (answers hidden) result transcript miss))
  have finite : (budget : ENNReal) / baseFieldModulus ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by norm_num [baseFieldModulus])
  exact bound.trans ((ENNReal.toReal_mono finite hit).trans_eq (by simp))

/-- This equivalence swaps a hash value with its independent replacement. -/
def hashResampleEquiv (hidden : BaseField) :
    (EncPRF.HashOracle × (Block × Block)) ≃ (EncPRF.HashOracle × (Block × Block)) where
  toFun sample := (Function.update sample.1 hidden sample.2, sample.1 hidden)
  invFun sample := (Function.update sample.1 hidden sample.2, sample.1 hidden)
  left_inv sample := by
    apply Prod.ext
    · funext input
      by_cases same : input = hidden <;> simp [Function.update, same]
    · simp
  right_inv sample := by
    apply Prod.ext
    · funext input
      by_cases same : input = hidden <;> simp [Function.update, same]
    · simp

/-- An independent uniform replacement preserves the uniform random-oracle tape. -/
theorem map_uniform_hash_resample [Fintype Block] (hidden : BaseField) :
    (PMF.uniformOfFintype (EncPRF.HashOracle × (Block × Block))).map
        (fun sample => Function.update sample.1 hidden sample.2) =
      PMF.uniformOfFintype EncPRF.HashOracle := by
  change (PMF.uniformOfFintype (EncPRF.HashOracle × (Block × Block))).map
    (Prod.fst ∘ hashResampleEquiv hidden) = _
  rw [← PMF.map_comp, uniform_map_equiv]
  exact uniform_map_fst

end

end Kriterion.ArgoMAC.Security
