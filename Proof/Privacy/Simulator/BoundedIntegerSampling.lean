import Proof.Privacy.Simulator.OperationalOracle
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Option

namespace Kriterion.ArgoMAC.Security.BoundedIntegerSampling
open scoped ENNReal

private theorem tsum_option {A : Type} [Fintype A] (f : Option A → ENNReal) :
    (∑' value, f value) = f none + ∑' value, f (some value) := by
  simp only [tsum_fintype, Fintype.sum_option]

/-- Each random instruction reads one block of independent fair bits. -/
inductive BitCode (A : Type) where
  | pure (value : A)
  | bits (width : Nat) (next : Fin (2 ^ width) → BitCode A)

noncomputable def BitCode.law {A : Type} : BitCode A → PMF A
  | .pure value => PMF.pure value
  | .bits width next =>
      letI : Nonempty (Fin (2 ^ width)) := ⟨⟨0, Nat.two_pow_pos width⟩⟩
      (PMF.uniformOfFintype (Fin (2 ^ width))).bind fun block => (next block).law

/-- This interpreter counts every fair bit that the random source supplies. -/
def BitCode.run {A State : Type}
    (source : (width : Nat) → State → Fin (2 ^ width) × State) :
    BitCode A → State → (A × State) × Nat
  | .pure value, state => ((value, state), 0)
  | .bits width next, state =>
      let sampled := source width state
      let remaining := (next sampled.1).run source sampled.2
      (remaining.1, width + remaining.2)

/-- This width leaves at least one half of the block values acceptable. -/
def width (size : Nat) : Nat := size.log2 + 1

def blockSize (size : Nat) : Nat := 2 ^ width size

theorem size_lt_blockSize (size : Nat) : size < blockSize size := Nat.lt_log2_self

theorem blockSize_pos (size : Nat) : 0 < blockSize size := Nat.two_pow_pos _

theorem blockSize_le_twice (size : Nat) (positive : 0 < size) : blockSize size ≤ 2 * size := by
  have lower := Nat.log2_self_le (Nat.ne_of_gt positive)
  simpa only [blockSize, width, pow_succ, Nat.mul_comm] using Nat.mul_le_mul_right 2 lower

/-- The comparison accepts exactly the integers in the requested range. -/
def accept (size : Nat) (block : Fin (blockSize size)) : Option (Fin size) :=
  if within : block.val < size then some ⟨block.val, within⟩ else none

/-- The cutoff returns failure after the specified number of rejected blocks. -/
def cutoff (size : Nat) : Nat → BitCode (Option (Fin size))
  | 0 => .pure none
  | attempts + 1 => .bits (width size) fun block =>
      match accept size block with
      | some value => .pure (some value)
      | none => cutoff size attempts

noncomputable def trial (size : Nat) : PMF (Option (Fin size)) :=
  letI : Nonempty (Fin (blockSize size)) := ⟨⟨0, blockSize_pos size⟩⟩
  (PMF.uniformOfFintype (Fin (blockSize size))).map (accept size)

private theorem accept_eq_some (size : Nat) (block : Fin (blockSize size)) (value : Fin size) :
    accept size block = some value ↔
      block = ⟨value.val, Nat.lt_trans value.isLt (size_lt_blockSize size)⟩ := by
  unfold accept
  split
  · simp only [Option.some.injEq, Fin.ext_iff]
  · constructor
    · intro impossible; contradiction
    · intro same
      have eq : block.val = value.val := congrArg (fun x : Fin (blockSize size) => x.val) same
      have := value.isLt
      omega

/-- One successful value has exactly one block preimage. -/
theorem trial_some (size : Nat) (value : Fin size) :
    trial size (some value) = (blockSize size : ENNReal)⁻¹ := by
  classical
  unfold trial
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  simp_rw [@eq_comm _ (some value), accept_eq_some]
  exact tsum_ite_eq _ _

/-- This value is the one-attempt rejection probability. -/
noncomputable def rejection (size : Nat) : ENNReal :=
  ((blockSize size - size : Nat) : ENNReal) / blockSize size

private theorem rejection_add_success (size : Nat) :
    rejection size + (size : ENNReal) / blockSize size = 1 := by
  rw [rejection, ← ENNReal.add_div, ← Nat.cast_add,
    Nat.sub_add_cancel (Nat.le_of_lt (size_lt_blockSize size))]
  exact ENNReal.div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (blockSize_pos size)))
    (ENNReal.natCast_ne_top _)

/-- The trial fails on exactly the excess block values. -/
theorem trial_none (size : Nat) : trial size none = rejection size := by
  have total := (trial size).tsum_coe
  rw [tsum_option] at total
  simp_rw [trial_some] at total
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← div_eq_mul_inv] at total
  exact (ENNReal.add_left_inj (ENNReal.div_ne_top (ENNReal.natCast_ne_top size)
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (blockSize_pos size))))).mp
      (total.trans (rejection_add_success size).symm)

/-- One cutoff step first executes the actual block trial. -/
theorem cutoff_succ_law (size attempts : Nat) :
    (cutoff size (attempts + 1)).law = (trial size).bind
      (fun answer => match answer with
        | some value => PMF.pure (some value)
        | none => (cutoff size attempts).law) := by
  simp only [cutoff, BitCode.law, trial, PMF.bind_map, Function.comp_def]
  congr 1
  funext block
  cases accept size block <;> rfl

/-- The cutoff failure probability is the exact geometric tail. -/
theorem cutoff_none (size attempts : Nat) :
    (cutoff size attempts).law none = rejection size ^ attempts := by
  induction attempts with
  | zero => simp [cutoff, BitCode.law, PMF.pure_apply]
  | succ attempts ih =>
      rw [cutoff_succ_law, PMF.bind_apply, tsum_option]
      simp only [trial_none, PMF.pure_apply, reduceCtorEq, if_false,
        mul_zero, tsum_zero, add_zero, ih, pow_succ']

/-- Each accepted value has the same cutoff mass. -/
theorem cutoff_some (size attempts : Nat) (value : Fin size) :
    (cutoff size attempts).law (some value) =
      (∑ index ∈ Finset.range attempts, rejection size ^ index) / blockSize size := by
  induction attempts with
  | zero => simp [cutoff, BitCode.law, PMF.pure_apply]
  | succ attempts ih =>
      rw [cutoff_succ_law, PMF.bind_apply, tsum_option]
      simp only [trial_none, trial_some, PMF.pure_apply, Option.some.injEq]
      simp_rw [mul_ite, mul_zero]
      simp_rw [@eq_comm (Fin size) value, mul_one]
      rw [tsum_ite_eq]
      rw [ih]
      rw [Finset.sum_range_succ', ENNReal.add_div]
      simp only [pow_zero, one_div, pow_succ']
      rw [← Finset.mul_sum, mul_div_assoc]

/-- The cutoff consumes at most its block width times its retry limit. -/
theorem cutoff_run_bits_le {State : Type}
    (source : (width : Nat) → State → Fin (2 ^ width) × State)
    (size attempts : Nat) (state : State) :
    ((cutoff size attempts).run source state).2 ≤ width size * attempts := by
  induction attempts generalizing state with
  | zero => simp [cutoff, BitCode.run]
  | succ attempts ih =>
      simp only [cutoff, BitCode.run]
      split
      · simp [BitCode.run, Nat.mul_succ]
      · have bound := ih (source (width size) state).2
        simp only [Nat.mul_succ]
        omega

/-- Each positive range rejects at most one half of the bit blocks. -/
theorem rejection_le_half (size : Nat) (positive : 0 < size) :
    rejection size ≤ (2 : ENNReal)⁻¹ := by
  rw [rejection, ENNReal.div_le_iff
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (blockSize_pos size))) (ENNReal.natCast_ne_top _)]
  rw [mul_comm]
  change ((blockSize size - size : Nat) : ENNReal) ≤ (blockSize size : ENNReal) / 2
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
  have bound := blockSize_le_twice size positive
  have cover := size_lt_blockSize size
  have arithmetic : (blockSize size - size) * 2 ≤ blockSize size := by omega
  exact_mod_cast arithmetic

/-- The finite sampler has an explicit geometric failure bound. -/
theorem cutoff_failure_le (size : Nat) (positive : 0 < size) (attempts : Nat) :
    (cutoff size attempts).law none ≤ (2 : ENNReal)⁻¹ ^ attempts := by
  rw [cutoff_none]
  exact pow_le_pow_left' (rejection_le_half size positive) attempts

/-- The 256-retry sampler fails with probability at most two to the minus 256. -/
theorem cutoff256_failure_le (size : Nat) (positive : 0 < size) :
    (cutoff size 256).law none ≤ ((2 : ENNReal) ^ 256)⁻¹ := by
  simpa only [ENNReal.inv_pow] using cutoff_failure_le size positive 256

/-- The successful cutoff mass is its total success probability times the uniform law. -/
theorem cutoff_success_submass (size : Nat) (positive : 0 < size)
    (attempts : Nat) (value : Fin size) :
    (cutoff size attempts).law (some value) =
      (1 - rejection size ^ attempts) / (size : ENNReal) := by
  have same (other : Fin size) :
      (cutoff size attempts).law (some other) = (cutoff size attempts).law (some value) := by
    rw [cutoff_some, cutoff_some]
  have total := (cutoff size attempts).law.tsum_coe
  rw [tsum_option, cutoff_none] at total
  simp_rw [same] at total
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at total
  have product : (size : ENNReal) * (cutoff size attempts).law (some value) =
      1 - rejection size ^ attempts := by
    apply ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top
    simpa only [add_comm] using total
  rw [← product, mul_comm]
  exact (ENNReal.mul_div_cancel_right (Nat.cast_ne_zero.mpr (Nat.ne_of_gt positive))
    (ENNReal.natCast_ne_top size)).symm

/-- This mass sums the mutually exclusive first-success events. -/
noncomputable def eventualMass (size : Nat) (_value : Fin size) : ENNReal :=
  ∑' attempts : Nat, rejection size ^ attempts / blockSize size

/-- The exact mass is the increasing limit of the executable finite cutoffs. -/
theorem eventualMass_eq_iSup_cutoff (size : Nat) (value : Fin size) :
    eventualMass size value = ⨆ attempts : Nat, (cutoff size attempts).law (some value) := by
  unfold eventualMass
  rw [ENNReal.tsum_eq_iSup_nat]
  congr 1
  funext attempts
  simp only [cutoff_some, div_eq_mul_inv, Finset.sum_mul]

/-- The exact rejection sampler has the uniform finite output law. -/
theorem eventualMass_uniform (size : Nat) (_positive : 0 < size) (value : Fin size) :
    eventualMass size value = (size : ENNReal)⁻¹ := by
  have complement : 1 - rejection size = (size : ENNReal) / blockSize size :=
    ENNReal.sub_eq_of_eq_add_rev' ENNReal.one_ne_top (rejection_add_success size).symm
  unfold eventualMass
  simp_rw [div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, complement,
    ENNReal.inv_div (Or.inl (ENNReal.natCast_ne_top _))
      (Or.inl (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (blockSize_pos size))))]
  rw [div_eq_mul_inv]
  calc
    _ = (size : ENNReal)⁻¹ * ((blockSize size : ENNReal) * (blockSize size : ENNReal)⁻¹) := by ac_rfl
    _ = _ := by
      rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (blockSize_pos size)))
        (ENNReal.natCast_ne_top _), mul_one]

/-- The exact law uses the summed first-success masses. -/
noncomputable def exactLaw (size : Nat) (positive : 0 < size) : PMF (Fin size) := by
  letI : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
  refine ⟨eventualMass size, ?_⟩
  have same : eventualMass size = PMF.uniformOfFintype (Fin size) := by
    funext value
    simp only [eventualMass_uniform size positive, PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [same]
  exact (PMF.uniformOfFintype (Fin size)).hasSum_coe_one

theorem exactLaw_uniform (size : Nat) (positive : 0 < size) :
    letI : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
    exactLaw size positive = PMF.uniformOfFintype (Fin size) := by
  letI : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
  apply PMF.ext
  intro value
  exact (eventualMass_uniform size positive value).trans (by simp [PMF.uniformOfFintype_apply])

/-- The tail sum counts the expected number of attempted bit blocks. -/
noncomputable def expectedAttempts (size : Nat) : ENNReal :=
  ∑' attempts : Nat, (cutoff size attempts).law none

theorem expectedAttempts_le_two (size : Nat) (positive : 0 < size) :
    expectedAttempts size ≤ 2 := by
  calc
    _ ≤ ∑' attempts : Nat, (2 : ENNReal)⁻¹ ^ attempts :=
      ENNReal.tsum_le_tsum fun attempts => cutoff_failure_le size positive attempts
    _ = 2 := ENNReal.tsum_geometric_two

/-- The exact sampler has expected bit cost equal to its block width times its tail sum. -/
noncomputable def expectedFairBits (size : Nat) : ENNReal :=
  (width size : ENNReal) * expectedAttempts size

/-- A range of at most 256 bits needs blocks of at most 257 bits. -/
theorem width_le_257 (size : Nat) (positive : 0 < size) (bounded : size ≤ 2 ^ 256) :
    width size ≤ 257 := by
  have lower := Nat.log2_self_le (Nat.ne_of_gt positive)
  have power : 2 ^ size.log2 ≤ 2 ^ 256 := lower.trans bounded
  have logarithm := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp power
  unfold width
  omega

/-- The exact sampler needs at most 514 fair bits in expectation. -/
theorem expectedFairBits_le_514 (size : Nat) (positive : 0 < size)
    (bounded : size ≤ 2 ^ 256) : expectedFairBits size ≤ 514 := by
  calc
    _ ≤ (257 : ENNReal) * 2 := mul_le_mul'
      (by exact_mod_cast width_le_257 size positive bounded) (expectedAttempts_le_two size positive)
    _ = 514 := by norm_num

/-- The cutoff has a strict bit bound for every random tape. -/
theorem cutoff_run_bits_le_257 {State : Type}
    (source : (width : Nat) → State → Fin (2 ^ width) × State)
    (size : Nat) (positive : 0 < size) (bounded : size ≤ 2 ^ 256)
    (attempts : Nat) (state : State) :
    ((cutoff size attempts).run source state).2 ≤ 257 * attempts :=
  (cutoff_run_bits_le source size attempts state).trans
    (Nat.mul_le_mul_right attempts (width_le_257 size positive bounded))

end Kriterion.ArgoMAC.Security.BoundedIntegerSampling
