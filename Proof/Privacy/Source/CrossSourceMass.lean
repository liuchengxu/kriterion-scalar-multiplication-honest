import Proof.Privacy.Transcript.AdaptiveGameRatio

namespace Kriterion.ArgoMAC.Security
open Cryptography
open scoped ENNReal
noncomputable section

/-- The program factor can use a compatible reference from another handler. -/
theorem selectedProgram_transcript_mass_factor_cross
    {oracle : OracleSpec} {Source State Other Key Result : Type}
    (handler : OracleHandler oracle State) (other : OracleHandler oracle Other) {budget : Nat}
    (program : Key → OracleProgram oracle Result budget)
    (samples : PMF Source) (select : Source → Key) (state : Source → State)
    (reference : Other) (key : Key) (result : Result)
    (transcript : List (Sigma oracle.Answer))
    (compatible : OracleTranscriptCompatible other reference transcript) :
    (samples.bind fun sample =>
      ((runOracleProgramWithTranscript handler (program (select sample)) (state sample)).map
        fun output => (select sample, output.1, output.2.2))) (key, result, transcript) =
      ((runOracleProgramWithTranscript other (program key) reference).map
        (fun output => (output.1, output.2.2))) (result, transcript) *
      samples.toOuterMeasure {sample | select sample = key ∧
        OracleTranscriptCompatible handler (state sample) transcript} := by
  classical
  rw [PMF.bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro sample
  by_cases same : select sample = key
  · have tagged : ∀ distribution : PMF (Result × State × List (Sigma oracle.Answer)),
        (distribution.map fun output => (select sample, output.1, output.2.2))
          (key, result, transcript) =
        (distribution.map fun output => (output.1, output.2.2)) (result, transcript) := by
      intro distribution
      simp only [PMF.map_apply, same, Prod.mk.injEq, true_and]
    rw [tagged, same]
    by_cases matching : OracleTranscriptCompatible handler (state sample) transcript
    · simp only [Set.indicator_apply, Set.mem_setOf_eq, same, matching, and_self, if_true]
      rw [runOracleProgramWithTranscript_mass_eq handler other (program key)
        (state sample) reference result transcript matching compatible, mul_comm]
    · simp only [Set.indicator_apply, Set.mem_setOf_eq, same, matching, and_false, if_false,
        mul_zero]
      rw [runOracleProgramWithTranscript_mass_zero handler (program key) (state sample)
        result transcript matching, mul_zero]
  · simp [PMF.map_apply, same, Ne.symm same]

/-- Both phases use the same external reference handler. -/
theorem twoPhaseTranscript_mass_factor_cross {oracle : OracleSpec.{0, 0}}
    {State Other First Labels Second : Type}
    (handler : OracleHandler oracle State) (other : OracleHandler oracle Other) {firstBudget secondBudget : Nat}
    (choose : OracleProgram oracle First firstBudget)
    (encode : State → First → PMF (Labels × State))
    (decide : First → Labels → OracleProgram oracle Second secondBudget)
    (state : State) (referenceBefore referenceAfter : Other)
    (selected : First) (labels : Labels) (decision : Second)
    (before after : List (Sigma oracle.Answer))
    (firstCompatible : OracleTranscriptCompatible other referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible other referenceAfter after) :
    twoPhaseTranscript handler choose encode decide state
      (selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript other choose referenceBefore).map
      (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript other (decide selected labels) referenceAfter).map
      (fun output => (output.1, output.2.2))) (decision, after) *
    twoPhaseSourceMass handler encode state selected labels before after := by
  rw [twoPhaseTranscript_first_mass]
  rw [selectedProgram_transcript_mass_factor_cross handler other (decide selected)
    (encode (transcriptFinalState handler state before) selected) Prod.fst Prod.snd
    referenceAfter labels decision after secondCompatible]
  by_cases compatible : OracleTranscriptCompatible handler state before
  · rw [runOracleProgramWithTranscript_mass_eq handler other choose state referenceBefore
      selected before compatible firstCompatible]
    simp only [twoPhaseSourceMass, compatible, if_true, mul_assoc]
  · rw [runOracleProgramWithTranscript_mass_zero handler choose state selected before compatible]
    simp [twoPhaseSourceMass, compatible]


/-- The sampled source keeps the same factors under another reference handler. -/
theorem sampledTwoPhaseTranscript_mass_factor_cross {oracle : OracleSpec.{0, 0}}
    {Source State Other Public First Labels Second : Type}
    (handler : OracleHandler oracle State) (other : OracleHandler oracle Other) {firstBudget secondBudget : Nat}
    (samples : PMF Source) (table : Source → Public) (state : Source → State)
    (choose : Public → OracleProgram oracle First firstBudget)
    (encode : Source → State → First → PMF (Labels × State))
    (decide : Public → First → Labels → OracleProgram oracle Second secondBudget)
    (referenceBefore referenceAfter : Other)
    (publicTable : Public) (selected : First) (labels : Labels) (decision : Second)
    (before after : List (Sigma oracle.Answer))
    (firstCompatible : OracleTranscriptCompatible other referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible other referenceAfter after) :
    sampledTwoPhaseTranscript handler samples table state choose encode decide
      (publicTable, selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript other (choose publicTable) referenceBefore).map
      (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript other (decide publicTable selected labels) referenceAfter).map
      (fun output => (output.1, output.2.2))) (decision, after) *
    sampledTwoPhaseSourceMass handler samples table state encode
      publicTable selected labels before after := by
  classical
  rw [sampledTwoPhaseTranscript, PMF.bind_apply, sampledTwoPhaseSourceMass,
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro source
  by_cases same : table source = publicTable
  · have tagged : ∀ distribution : PMF (First × List (Sigma oracle.Answer) ×
          Labels × Second × List (Sigma oracle.Answer)),
        (distribution.map (Prod.mk (table source)))
          (publicTable, selected, before, labels, decision, after) =
        distribution (selected, before, labels, decision, after) := by
      intro distribution
      simp only [PMF.map_apply, same, Prod.mk.injEq, true_and]
      rw [tsum_eq_single (selected, before, labels, decision, after)]
      · simp
      · intro value different
        simp [Ne.symm different]
    rw [tagged, same, if_pos rfl,
      twoPhaseTranscript_mass_factor_cross handler other (choose publicTable) (encode source)
        (decide publicTable) (state source) referenceBefore referenceAfter
        selected labels decision before after firstCompatible secondCompatible]
    ac_rfl
  · simp [PMF.map_apply, same, Ne.symm same]


end
end Kriterion.ArgoMAC.Security
