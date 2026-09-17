/-
This file defines the hybrid chain from the active BaBe paper.
The paper proof is in `gc_rpm_proof.tex` and `gc_optimizations.tex`.
The paper source is https://github.com/babylonlabs-io/BaBe.latex/tree/e2dcf4d540b2708e13cd21090df759051119a116.
-/

import Construction.Garbling
import Cryptography.Assumptions
import Proof.Privacy.Distribution.PublicDistribution
import Security.AdaptivePrivacy

namespace Kriterion.ArgoMAC.Security

open GarbledCircuit
open Cryptography
open Cryptography.Assumptions

universe uKey uCounter uCTPRFIndex uEncPRFIndex uHashInput uCPAAux uSample
  uQuery uAnswer uResult uState

/-- The fixed AES block size in the paper is 128 bits. -/
def blockBits : Nat := 128

/-- The paper base-`(2 - omega)` case uses 92 active inputs per bucket. -/
def paperActiveInputsPerBucket : Nat := 92

/-- The paper proof uses 6858 independent permutation buckets. -/
def paperBucketCount : Nat := 6858

noncomputable def paperCTPRFError (securityParameter oracleQueries : Nat) : ℝ :=
  ((3 * paperBucketCount * paperActiveInputsPerBucket ^ 2 +
      4 * paperActiveInputsPerBucket * oracleQueries : Nat) : ℝ) /
    (2 : ℝ) ^ securityParameter

/-- This is the paper bound at the 128-bit AES block size. -/
noncomputable def paperConcreteCTPRFError (oracleQueries : Nat) : ℝ :=
  paperCTPRFError blockBits oracleQueries

/-- Every permutation query costs at least one unit of work. -/
def permutationWork (oracleQueries : Nat) : Nat := max oracleQueries 1

/-- The paper CTPRF bound gives at least 100 bits of concrete security. -/
theorem paperConcreteCTPRFHas100Bits :
    ConcreteBound 100 permutationWork paperConcreteCTPRFError := by
  intro queries
  have countBound :
      3 * paperBucketCount * paperActiveInputsPerBucket ^ 2 +
          4 * paperActiveInputsPerBucket * queries ≤ permutationWork queries * 2 ^ 28 := by
    cases queries with
    | zero => norm_num [paperBucketCount, paperActiveInputsPerBucket, permutationWork]
    | succ queries =>
        rw [permutationWork, Nat.max_eq_left (by omega : 1 ≤ queries + 1)]
        norm_num [paperBucketCount, paperActiveInputsPerBucket]
        omega
  rw [WorkPerAdvantage]
  change (((3 * paperBucketCount * paperActiveInputsPerBucket ^ 2 +
      4 * paperActiveInputsPerBucket * queries : Nat) : ℝ) /
      (2 : ℝ) ^ 128) * (2 : ℝ) ^ 100 ≤ ((permutationWork queries : Nat) : ℝ)
  calc
    (((3 * paperBucketCount * paperActiveInputsPerBucket ^ 2 +
        4 * paperActiveInputsPerBucket * queries : Nat) : ℝ) /
        (2 : ℝ) ^ 128) * (2 : ℝ) ^ 100 =
      ((3 * paperBucketCount * paperActiveInputsPerBucket ^ 2 +
        4 * paperActiveInputsPerBucket * queries : Nat) : ℝ) / (2 : ℝ) ^ 28 := by
        norm_num [div_eq_mul_inv]
        ring
    _ ≤ ((permutationWork queries : Nat) : ℝ) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 28)).2
      norm_num
      exact_mod_cast countBound

/-- Each fixed-key permutation serves one branch of every gate in its bucket.
A point bucket holds `digitsPerBucket` gates with one label pair and distinct tweaks.
A curve bucket holds one gate. The paper events `bad2`, `bad4`, and `bad3` give
`Q ^ 2 / 2 + 2 * Q * q` per permutation. This formula sums them. -/
noncomputable def bucketedCTPRFError (oracleQueries : Nat) : ℝ :=
  ((Pipeline.pointBucketCount * Pipeline.digitsPerBucket ^ 2 + Pipeline.curveBucketCount +
      4 * Pipeline.digitsPerBucket * oracleQueries : Nat) : ℝ) /
    (2 : ℝ) ^ (blockBits + 1)

/-- The bucketed schedule gives at least 100 bits of concrete security. -/
theorem bucketedCTPRFHas100Bits :
    ConcreteBound 100 permutationWork bucketedCTPRFError := by
  intro queries
  have countBound :
      Pipeline.pointBucketCount * Pipeline.digitsPerBucket ^ 2 + Pipeline.curveBucketCount +
          4 * Pipeline.digitsPerBucket * queries ≤ permutationWork queries * 2 ^ 29 := by
    change 126208790 + 364 * queries ≤ max queries 1 * 536870912
    omega
  rw [WorkPerAdvantage]
  change (((Pipeline.pointBucketCount * Pipeline.digitsPerBucket ^ 2 +
      Pipeline.curveBucketCount + 4 * Pipeline.digitsPerBucket * queries : Nat) : ℝ) /
      (2 : ℝ) ^ (128 + 1)) * (2 : ℝ) ^ 100 ≤ ((permutationWork queries : Nat) : ℝ)
  calc
    (((Pipeline.pointBucketCount * Pipeline.digitsPerBucket ^ 2 +
        Pipeline.curveBucketCount + 4 * Pipeline.digitsPerBucket * queries : Nat) : ℝ) /
        (2 : ℝ) ^ (128 + 1)) * (2 : ℝ) ^ 100 =
      ((Pipeline.pointBucketCount * Pipeline.digitsPerBucket ^ 2 +
        Pipeline.curveBucketCount + 4 * Pipeline.digitsPerBucket * queries : Nat) : ℝ) /
        (2 : ℝ) ^ 29 := by
        norm_num [div_eq_mul_inv]
        ring
    _ ≤ ((permutationWork queries : Nat) : ℝ) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 29)).2
      norm_num
      exact_mod_cast countBound

/-- This value counts all bit-adaptor evaluations in one circuit. -/
def bitAdaptorEvaluationCount : Nat :=
  Pipeline.digitAdaptorCount * coordinateBitCount

theorem bitAdaptorEvaluationCountValue : bitAdaptorEvaluationCount = 278638 := by decide

/-- This event records one selected gate's rejected hash-lift suffix. -/
def dependentHashLiftBadEvent
    (location : Fin bitAdaptorEvaluationCount →
      GarblingRandomnessRest → Pipeline.FixedKeyLocation)
    (window : Fin bitAdaptorEvaluationCount → GarblingRandomnessRest → Nat)
    (label : Fin bitAdaptorEvaluationCount → GarblingRandomnessRest → Block)
    (index : Fin bitAdaptorEvaluationCount) : Set Garbling.Randomness :=
  fun randomness => hashLiftSplitEquiv
    (fixedDaviesMeyerHashLift
      (location index (garblingRandomnessRest randomness))
      (window index (garblingRandomnessRest randomness))
      (label index (garblingRandomnessRest randomness))
      randomness.fixedKeyOracle) ∈ hashLiftBadSet

/-- Each selected dependent-label event has the exact complete-tape mass. -/
theorem randomTape_dependentHashLiftBadEvent_mass
    (witness : Garbling.Randomness) (parameter : Nat)
    (location : Fin bitAdaptorEvaluationCount →
      GarblingRandomnessRest → Pipeline.FixedKeyLocation)
    (window : Fin bitAdaptorEvaluationCount → GarblingRandomnessRest → Nat)
    (label : Fin bitAdaptorEvaluationCount → GarblingRandomnessRest → Block)
    (index : Fin bitAdaptorEvaluationCount) :
    (randomTape witness parameter).toOuterMeasure
        (dependentHashLiftBadEvent location window label index) =
      ((2 ^ 384 % BN254.baseFieldModulus : Nat) : ENNReal) /
        ((2 ^ 384 : Nat) : ENNReal) := by
  rw [← randomTape_dependentGateDaviesMeyerHashSplit_badMass witness parameter
    (location index) (window index) (label index)]
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-- This is the aggregate mass bound for all selected hash lifts. -/
noncomputable def hashLiftAggregateMass : ENNReal :=
  ((bitAdaptorEvaluationCount * BN254.baseFieldModulus : Nat) : ENNReal) /
    ((2 ^ 384 : Nat) : ENNReal)

set_option exponentiation.threshold 400 in
/-- All selected hash-lift failures have this aggregate outer-measure bound. -/
theorem selectedHashLiftBadUnion_mass_le
    {Sample : Type uSample} (measure : MeasureTheory.OuterMeasure Sample)
    (event : Fin bitAdaptorEvaluationCount → Set Sample)
    (localBound : ∀ index, measure (event index) ≤
      (BN254.baseFieldModulus : ENNReal) / ((2 ^ 384 : Nat) : ENNReal)) :
    measure (⋃ index, event index) ≤ hashLiftAggregateMass := by
  calc
    measure (⋃ index, event index) ≤
        (Fintype.card (Fin bitAdaptorEvaluationCount) : ENNReal) *
          ((BN254.baseFieldModulus : ENNReal) /
            ((2 ^ 384 : Nat) : ENNReal)) :=
      finiteBadEventUnionMass_le measure event _ localBound
    _ = hashLiftAggregateMass := by
      have castProduct :
          ((bitAdaptorEvaluationCount * BN254.baseFieldModulus : Nat) : ENNReal) =
            (bitAdaptorEvaluationCount : ENNReal) *
              (BN254.baseFieldModulus : ENNReal) := by
        exact_mod_cast (Nat.cast_mul bitAdaptorEvaluationCount
          BN254.baseFieldModulus :
            (bitAdaptorEvaluationCount * BN254.baseFieldModulus : Nat) = _)
      rw [hashLiftAggregateMass, Fintype.card_fin, castProduct]
      simp only [div_eq_mul_inv]
      ring

set_option exponentiation.threshold 400 in
/-- All dependent-label gate failures have the aggregate security-tape bound. -/
theorem selectedDependentHashLiftBadUnion_mass_le
    (witness : Garbling.Randomness) (parameter : Nat)
    (location : Fin bitAdaptorEvaluationCount →
      GarblingRandomnessRest → Pipeline.FixedKeyLocation)
    (window : Fin bitAdaptorEvaluationCount → GarblingRandomnessRest → Nat)
    (label : Fin bitAdaptorEvaluationCount → GarblingRandomnessRest → Block) :
    (randomTape witness parameter).toOuterMeasure
        (⋃ index, dependentHashLiftBadEvent location window label index) ≤
      hashLiftAggregateMass := by
  apply selectedHashLiftBadUnion_mass_le
  intro index
  rw [randomTape_dependentHashLiftBadEvent_mass]
  apply ENNReal.div_le_div_right
  exact_mod_cast hashLiftRemainder_lt_baseFieldModulus.le

/-- This is the bound shape for the total 384-bit lift rounding term. -/
noncomputable def hashLiftRoundingError : ℝ :=
  ((bitAdaptorEvaluationCount * BN254.baseFieldModulus : Nat) : ℝ) / (2 : ℝ) ^ 384

set_option exponentiation.threshold 400 in
/-- The aggregate mass converts to the challenge's real-valued error term. -/
theorem hashLiftAggregateMass_toReal :
    hashLiftAggregateMass.toReal = hashLiftRoundingError := by
  rw [hashLiftAggregateMass, hashLiftRoundingError, ENNReal.toReal_div]
  norm_num

set_option exponentiation.threshold 400 in
/-- The real mass of all selected lift failures is at most the declared error. -/
theorem selectedHashLiftBadUnion_toReal_le
    {Sample : Type uSample} (measure : MeasureTheory.OuterMeasure Sample)
    (event : Fin bitAdaptorEvaluationCount → Set Sample)
    (localBound : ∀ index, measure (event index) ≤
      (BN254.baseFieldModulus : ENNReal) / ((2 ^ 384 : Nat) : ENNReal)) :
    (measure (⋃ index, event index)).toReal ≤ hashLiftRoundingError := by
  rw [← hashLiftAggregateMass_toReal]
  apply ENNReal.toReal_mono
  · rw [hashLiftAggregateMass]
    apply ENNReal.div_ne_top
    · have castProduct :
          ((bitAdaptorEvaluationCount * BN254.baseFieldModulus : Nat) : ENNReal) =
            (bitAdaptorEvaluationCount : ENNReal) *
              (BN254.baseFieldModulus : ENNReal) := by
          exact_mod_cast (Nat.cast_mul bitAdaptorEvaluationCount
            BN254.baseFieldModulus :
              (bitAdaptorEvaluationCount * BN254.baseFieldModulus : Nat) = _)
      rw [castProduct]
      exact ENNReal.mul_ne_top (by simp) (by simp)
    · norm_num
  · exact selectedHashLiftBadUnion_mass_le measure event localBound

set_option exponentiation.threshold 400 in
/-- The real dependent-label union mass is at most the rounding error. -/
theorem selectedDependentHashLiftBadUnion_toReal_le
    (witness : Garbling.Randomness) (parameter : Nat)
    (location : Fin bitAdaptorEvaluationCount →
      GarblingRandomnessRest → Pipeline.FixedKeyLocation)
    (window : Fin bitAdaptorEvaluationCount → GarblingRandomnessRest → Nat)
    (label : Fin bitAdaptorEvaluationCount → GarblingRandomnessRest → Block) :
    ((randomTape witness parameter).toOuterMeasure
        (⋃ index, dependentHashLiftBadEvent location window label index)).toReal ≤
      hashLiftRoundingError := by
  apply selectedHashLiftBadUnion_toReal_le
  intro index
  rw [randomTape_dependentHashLiftBadEvent_mass]
  apply ENNReal.div_le_div_right
  exact_mod_cast hashLiftRemainder_lt_baseFieldModulus.le

/-- This schedule contains the real selected locations, windows, and labels. -/
def selectedGateMetadataSchedule (rest : GarblingRandomnessRest)
    (input : BN254.AffineInput) : List GateDirective :=
  let curve := defaultSimulatorCoin.tableSample.curveRequest.retarget input
    rest.algebraic.field.bridgeKey
  let curveInputMac := rest.inputMacKey.encodeAffine input
  let pointInputMac := EncPRF.transformMac rest.encPRFOracle
    (EncPRF.whiteningKeys rest.hashOracle rest.algebraic.field.bridgeKey)
    (BitInput.ofAffine input) curveInputMac
  pipelineGateSchedule curve defaultSimulatorCoin.tableSample.pointRequests input
    curveInputMac pointInputMac

/-- The selected metadata schedule contains all 301,752 gates. -/
theorem selectedGateMetadataSchedule_length (rest : GarblingRandomnessRest)
    (input : BN254.AffineInput) :
    (selectedGateMetadataSchedule rest input).length = bitAdaptorEvaluationCount := by
  rw [selectedGateMetadataSchedule, pipelineGateSchedule_length]
  rfl

/-- This value selects one gate from the complete metadata schedule. -/
def selectedGateMetadataDirective (rest : GarblingRandomnessRest)
    (input : BN254.AffineInput)
    (index : Fin bitAdaptorEvaluationCount) : GateDirective :=
  (selectedGateMetadataSchedule rest input).get ⟨index.val, by
    rw [selectedGateMetadataSchedule_length]
    exact index.isLt⟩

/-- This event records one actual selected gate's rejected hash lift. -/
def selectedGateHashBadEvent (input : BN254.AffineInput)
    (index : Fin bitAdaptorEvaluationCount) : Set Garbling.Randomness :=
  dependentHashLiftBadEvent
    (fun selected rest => (selectedGateMetadataDirective rest input selected).location)
    (fun selected rest => (selectedGateMetadataDirective rest input selected).window)
    (fun selected rest => (selectedGateMetadataDirective rest input selected).label)
    index

set_option exponentiation.threshold 400 in
/-- The actual selected gate suffix union has the aggregate security-tape bound. -/
theorem selectedGateHashBadUnion_mass_le
    (witness : Garbling.Randomness) (parameter : Nat)
    (input : BN254.AffineInput) :
    (randomTape witness parameter).toOuterMeasure
        (⋃ index, selectedGateHashBadEvent input index) ≤ hashLiftAggregateMass := by
  exact selectedDependentHashLiftBadUnion_mass_le witness parameter
    (fun selected rest => (selectedGateMetadataDirective rest input selected).location)
    (fun selected rest => (selectedGateMetadataDirective rest input selected).window)
    (fun selected rest => (selectedGateMetadataDirective rest input selected).label)

set_option exponentiation.threshold 400 in
/-- The real selected gate suffix union is at most the rounding error. -/
theorem selectedGateHashBadUnion_toReal_le
    (witness : Garbling.Randomness) (parameter : Nat)
    (input : BN254.AffineInput) :
    ((randomTape witness parameter).toOuterMeasure
        (⋃ index, selectedGateHashBadEvent input index)).toReal ≤
      hashLiftRoundingError := by
  exact selectedDependentHashLiftBadUnion_toReal_le witness parameter
    (fun selected rest => (selectedGateMetadataDirective rest input selected).location)
    (fun selected rest => (selectedGateMetadataDirective rest input selected).window)
    (fun selected rest => (selectedGateMetadataDirective rest input selected).label)

set_option exponentiation.threshold 400 in
/-- The total lift rounding term retains 100-bit arithmetic. -/
theorem hashLiftRoundingArithmeticHas100Bits :
    WorkPerAdvantage 100 1 hashLiftRoundingError := by
  rw [WorkPerAdvantage, hashLiftRoundingError, bitAdaptorEvaluationCountValue]
  norm_num [BN254.baseFieldModulus]

end Kriterion.ArgoMAC.Security
