import Proof.Privacy.Transcript.EncPRFTranscript
import Proof.Privacy.Distribution.HashQueryDistribution
import Proof.Shared.HCoefficient

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography
open scoped ENNReal

noncomputable section

/-- This law separates a selected program from its source constraints. -/
theorem selectedProgram_transcript_mass_factor
    {oracle : OracleSpec} {Source State Key Result : Type}
    (handler : OracleHandler oracle State) {budget : Nat}
    (program : Key → OracleProgram oracle Result budget)
    (samples : PMF Source) (select : Source → Key) (state : Source → State)
    (reference : State) (key : Key) (result : Result)
    (transcript : List (Sigma oracle.Answer))
    (compatible : OracleTranscriptCompatible handler reference transcript) :
    (samples.bind fun sample =>
      ((runOracleProgramWithTranscript handler (program (select sample)) (state sample)).map
        fun output => (select sample, output.1, output.2.2))) (key, result, transcript) =
      ((runOracleProgramWithTranscript handler (program key) reference).map
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
      rw [runOracleProgramWithTranscript_mass_eq handler handler (program key)
        (state sample) reference result transcript matching compatible, mul_comm]
    · simp only [Set.indicator_apply, Set.mem_setOf_eq, same, matching, and_false, if_false,
        mul_zero]
      rw [runOracleProgramWithTranscript_mass_zero handler (program key) (state sample)
        result transcript matching, mul_zero]
  · simp [PMF.map_apply, same, Ne.symm same]

variable [Fintype Block]

local instance : Fintype InputMacKey := publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

local instance (history : List (PermutationRecord EncPRF.PermutationIndex Block))
    (index : EncPRF.PermutationIndex) : Fintype (EncQueryDomain history index) := by
  classical
  unfold EncQueryDomain
  infer_instance

/-- This game derives its target key from fresh whitening keys. -/
def realEncPRFRun {Result : Type} {budget : Nat}
    (source : InputMacKey) (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget) :=
  (PMF.uniformOfFintype
    ((Block × Block) × PermutationOracle EncPRF.PermutationIndex Block)).bind fun sample =>
      let target := EncPRF.transformKey sample.2 ⟨sample.1.1, sample.1.2⟩ source
      (hashTranscriptRun (program target) {randomness with encPRFOracle := sample.2}).map
        (Prod.mk target)

/-- This game samples its target key independently of the oracle. -/
def idealEncPRFRun {Result : Type} {budget : Nat}
    (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget) :=
  (PMF.uniformOfFintype InputMacKey).bind fun target =>
    ((PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)).bind fun oracle =>
      hashTranscriptRun (program target) {randomness with encPRFOracle := oracle}).map
        (Prod.mk target)

/-- The real game has the exact source constraint factor. -/
theorem realEncPRFRun_mass {Result : Type} {budget : Nat}
    (source target : InputMacKey) (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget)
    (reference : PermutationOracle EncPRF.PermutationIndex Block) (result : Result)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler
      {randomness with encPRFOracle := reference} transcript) :
    realEncPRFRun source randomness program (target, result, transcript) =
      hashTranscriptRun (program target) {randomness with encPRFOracle := reference}
        (result, transcript) *
      (PMF.uniformOfFintype
        ((Block × Block) × PermutationOracle EncPRF.PermutationIndex Block)).toOuterMeasure
        {sample | EncPRF.transformKey sample.2 ⟨sample.1.1, sample.1.2⟩ source = target ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with encPRFOracle := sample.2} transcript} := by
  simpa only [Nat.cast_ofNat,realEncPRFRun, hashTranscriptRun, PMF.map_comp, Function.comp_def] using
    selectedProgram_transcript_mass_factor Garbling.oracleHandler program
      (PMF.uniformOfFintype
        ((Block × Block) × PermutationOracle EncPRF.PermutationIndex Block))
      (fun sample => EncPRF.transformKey sample.2 ⟨sample.1.1, sample.1.2⟩ source)
      (fun sample => {randomness with encPRFOracle := sample.2})
      {randomness with encPRFOracle := reference} target result transcript compatible

/-- The ideal game has the uniform key and exact oracle factors. -/
theorem idealEncPRFRun_mass {Result : Type} {budget : Nat}
    (target : InputMacKey) (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget)
    (reference : PermutationOracle EncPRF.PermutationIndex Block) (result : Result)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler
      {randomness with encPRFOracle := reference} transcript) :
    idealEncPRFRun randomness program (target, result, transcript) =
      (PMF.uniformOfFintype InputMacKey) target *
      (hashTranscriptRun (program target) {randomness with encPRFOracle := reference}
        (result, transcript) * encTranscriptFactor (encOracleTranscriptRecords transcript)) := by
  rw [idealEncPRFRun, bind_pair_apply]
  congr 1
  have factor := runOracleProgramWithTranscript_mass_factor
    Garbling.oracleHandler Garbling.oracleHandler (program target)
    ((PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)).map
      fun oracle => {randomness with encPRFOracle := oracle})
    {randomness with encPRFOracle := reference} result transcript compatible
  simp only [PMF.bind_map, PMF.map_bind, PMF.toOuterMeasure_map_apply,
    Function.comp_def] at factor
  simp only [hashTranscriptRun]
  rw [factor]
  congr 1
  have referenceMatches : PermutationTranscriptMatches reference (encOracleTranscriptRecords transcript) :=
    (realTranscript_update_enc_iff {randomness with encPRFOracle := reference}
      reference transcript compatible).mp compatible
  rw [← encTranscriptFactor_eq_mass reference _ referenceMatches]
  congr 1
  ext oracle
  exact realTranscript_update_enc_iff {randomness with encPRFOracle := reference}
    oracle transcript compatible

/-- Every supported ideal output has a compatible bounded reference transcript. -/
theorem idealEncPRFRun_supported {Result : Type} {budget : Nat}
    (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget)
    (output : InputMacKey × Result × List (Sigma Garbling.oracleSpec.Answer))
    (member : output ∈ (idealEncPRFRun randomness program).support) :
    output.2.2.length ≤ budget ∧ ∃ reference : PermutationOracle EncPRF.PermutationIndex Block,
      OracleTranscriptCompatible Garbling.oracleHandler
        {randomness with encPRFOracle := reference} output.2.2 := by
  simp only [idealEncPRFRun, PMF.mem_support_bind_iff, PMF.mem_support_map_iff,
    hashTranscriptRun] at member
  obtain ⟨target, _, observed, ⟨oracle, _, run, runMember, rfl⟩, rfl⟩ := member
  exact ⟨runOracleProgramWithTranscript_length_le Garbling.oracleHandler (program target) {randomness with encPRFOracle := oracle} run runMember,
    oracle, runOracleProgramWithTranscript_compatible Garbling.oracleHandler (program target) {randomness with encPRFOracle := oracle} run runMember⟩

/-- Every good adaptive transcript has the shared whitening-query ratio. -/
theorem encPRFRun_good_mass_ge {Result : Type} {budget : Nat}
    (source : InputMacKey) (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget)
    (fits : 2 + budget ≤ Fintype.card Block)
    (output : InputMacKey × Result × List (Sigma Garbling.oracleSpec.Answer))
    (distinct : ∀ index, Function.Injective (linkingPad source output.1 index)) :
    (1 - ((4 * budget : Nat) : ℝ≥0∞) / Fintype.card Block) *
      idealEncPRFRun randomness program output ≤ realEncPRFRun source randomness program output := by
  classical
  by_cases member : output ∈ (idealEncPRFRun randomness program).support
  · obtain ⟨lengthBound, reference, compatible⟩ := idealEncPRFRun_supported randomness program output member
    rcases output with ⟨target, result, transcript⟩
    have queryFits : ∀ index,
        2 + Fintype.card (EncQueryDomain (encOracleTranscriptRecords transcript) index) ≤
          Fintype.card Block := by
      intro index
      have each := Finset.single_le_sum (f := fun index =>
        Fintype.card (EncQueryDomain (encOracleTranscriptRecords transcript) index))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
      exact (Nat.add_le_add_left (each.trans ((encExternalQueryCount_le transcript).trans lengthBound)) 2).trans fits
    have bound := encFreshHashTranscript_mass_ge source target
      {randomness with encPRFOracle := reference} transcript compatible distinct budget lengthBound queryFits
    calc
      _ = hashTranscriptRun (program target) {randomness with encPRFOracle := reference}
          (result, transcript) *
          ((1 - ((4 * budget : Nat) : ℝ≥0∞) / Fintype.card Block) *
            (PMF.uniformOfFintype InputMacKey) target *
            encTranscriptFactor (encOracleTranscriptRecords transcript)) := by
        rw [idealEncPRFRun_mass target randomness program reference result transcript compatible]
        ac_rfl
      _ ≤ _ := mul_le_mul_right bound _
      _ = _ := (realEncPRFRun_mass source target randomness program reference result transcript compatible).symm
  · have zero : idealEncPRFRun randomness program output = 0 := by
      simpa only [Nat.cast_ofNat,PMF.mem_support_iff, not_not] using member
    simp only [zero, mul_zero, zero_le]

/-- The ideal transcript retains the uniform target-key marginal. -/
theorem idealEncPRFRun_key {Result : Type} {budget : Nat}
    (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget) :
    (idealEncPRFRun randomness program).map Prod.fst = PMF.uniformOfFintype InputMacKey := by
  simp only [idealEncPRFRun, PMF.map_bind, PMF.map_comp, Function.comp_def]
  calc
    _ = (PMF.uniformOfFintype InputMacKey).bind PMF.pure := by
      congr 1
      funext target
      simp only [PMF.map, Function.comp_def, PMF.bind_const]
    _ = _ := PMF.bind_pure _

/-- The full adaptive ideal run pays at most one pad collision per bucket. -/
theorem idealEncPRFRun_bad_mass_le {Result : Type} {budget : Nat}
    (source : InputMacKey) (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget) :
    (idealEncPRFRun randomness program).toOuterMeasure
      {output | ∃ index, linkingPad source output.1 index false =
        linkingPad source output.1 index true} ≤ (508 : ℝ≥0∞) / Fintype.card Block := by
  have bound := linkingPad_collision_mass_le source
  rw [← idealEncPRFRun_key randomness program, PMF.toOuterMeasure_map_apply] at bound
  exact bound

/-- Fresh whitening keys hide the linked target key from every bounded adaptive program. -/
theorem encPRFRun_event_bound {Result : Type} {budget : Nat}
    (source : InputMacKey) (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget)
    (fits : 2 + budget ≤ Fintype.card Block)
    (event : Set (InputMacKey × Result × List (Sigma Garbling.oracleSpec.Answer))) :
    |((realEncPRFRun source randomness program).toOuterMeasure event).toReal -
      ((idealEncPRFRun randomness program).toOuterMeasure event).toReal| ≤
        ((508 + 4 * budget : Nat) : ℝ) / Fintype.card Block := by
  classical
  have cardNonzero : (Fintype.card Block : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have finite (count : Nat) : (count : ℝ≥0∞) / Fintype.card Block ≠ ⊤ :=
    ENNReal.div_ne_top (by simp) cardNonzero
  have bound := hCoefficient_event (realEncPRFRun source randomness program)
    (idealEncPRFRun randomness program)
    {output | ∃ index, linkingPad source output.1 index false =
      linkingPad source output.1 index true} event
    ((508 : ℝ) / Fintype.card Block) (((4 * budget : Nat) : ℝ) / Fintype.card Block)
    (by positivity)
    (by
      have bad := ENNReal.toReal_mono (finite 508)
        (idealEncPRFRun_bad_mass_le source randomness program)
      simpa only [Nat.cast_ofNat,ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofNat] using bad)
    (by
      intro output good
      have distinct : ∀ index, Function.Injective (linkingPad source output.1 index) := by
        intro index
        apply (booleanPad_injective_iff _).mpr
        exact fun equal => good ⟨index, equal⟩
      have ratio := ENNReal.toReal_mono
        ((realEncPRFRun source randomness program).apply_ne_top output)
        (encPRFRun_good_mass_ge source randomness program fits output distinct)
      rw [ENNReal.toReal_mul] at ratio
      have loss := ENNReal.le_toReal_sub (a := 1) (finite (4 * budget))
      simp only [ENNReal.toReal_one, ENNReal.toReal_div, ENNReal.toReal_natCast] at loss
      exact (mul_le_mul_of_nonneg_right loss ENNReal.toReal_nonneg).trans ratio)
  simpa only [Nat.cast_ofNat,Nat.cast_add, add_div] using bound

end

end Kriterion.ArgoMAC.Security
