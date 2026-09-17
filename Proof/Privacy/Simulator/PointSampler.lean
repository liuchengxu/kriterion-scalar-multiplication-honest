/-
This file samples a uniform BN254 point from one uniform scalar.
The proof uses the existing field and group certificates.
-/

import Proof.Privacy.Distribution.PointDistribution
import Mathlib.FieldTheory.Finiteness

namespace Kriterion.ArgoMAC.Security

open BN254

private noncomputable def squareRoot [FieldCertificate] (x : BaseField) : BaseField :=
  Classical.epsilon fun y => y ^ 2 = x ^ 3 + 3

private theorem equal_y_of_square_and_sign [FieldCertificate] (x y z : BaseField)
    (hy : y ^ 2 = x ^ 3 + 3) (hz : z ^ 2 = x ^ 3 + 3)
    (sign : decide (y = squareRoot x) = decide (z = squareRoot x)) : y = z := by
  have root : (squareRoot x) ^ 2 = x ^ 3 + 3 := by
    exact Classical.epsilon_spec (p := fun y : BaseField => y ^ 2 = x ^ 3 + 3) ⟨y, hy⟩
  have hy' := (sq_eq_sq_iff_eq_or_eq_neg).mp (hy.trans root.symm)
  have hz' := (sq_eq_sq_iff_eq_or_eq_neg).mp (hz.trans root.symm)
  by_cases h : y = squareRoot x
  · have hz'' : z = squareRoot x := by simpa [h] using sign.symm
    exact h.trans hz''.symm
  · have hz'' : z ≠ squareRoot x := by simpa [h] using sign.symm
    exact (hy'.resolve_left h).trans (hz'.resolve_left hz'').symm

private noncomputable def pointCode [FieldCertificate] : Point → Option (BaseField × Bool)
  | .zero => none
  | .some (x := x) (y := y) _ => some (x, decide (y = squareRoot x))

private theorem pointCode_injective [FieldCertificate] : Function.Injective pointCode := by
  intro first second equal
  cases first with
  | zero => cases second <;> simp_all [pointCode]
  | @some x y hy =>
    cases second with
    | zero => simp_all [pointCode]
    | @some u v hv =>
      have coords := Option.some.inj equal
      have sameX : x = u := congrArg Prod.fst coords
      subst u
      have sign : decide (y = squareRoot x) = decide (v = squareRoot x) :=
        congrArg Prod.snd coords
      have firstEquation := (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
        discriminantNeZero).mpr hy
      have secondEquation := (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
        discriminantNeZero).mpr hv
      have firstSquare := (equation_iff_onCurve { x, y }).mp firstEquation
      have secondSquare := (equation_iff_onCurve { x, y := v }).mp secondEquation
      have sameY := equal_y_of_square_and_sign x y v firstSquare secondSquare sign
      subst v
      rfl

attribute [local irreducible] pointCode pointFintype

/-- Each x-coordinate has at most two points. The identity adds one point. -/
theorem point_card_upper_bound [FieldCertificate] :
    Fintype.card Point ≤ 2 * baseFieldModulus + 1 := by
  have size {α : Type} [Fintype α] :
      Fintype.card (Option (α × Bool)) = 2 * Fintype.card α + 1 := by
    rw [Fintype.card_option, Fintype.card_prod, Fintype.card_bool]
    omega
  exact (Fintype.card_le_of_injective pointCode pointCode_injective).trans_eq
    ((size (α := BaseField)).trans (congrArg (fun count => 2 * count + 1) (ZMod.card _)))

/-- The certified group has exactly one scalar-field dimension. -/
theorem point_card_eq_scalar [FieldCertificate] [GroupCertificate] :
    Fintype.card Point = scalarFieldModulus := by
  letI : Fact (Nat.Prime scalarFieldModulus) := ⟨scalarFieldPrime⟩
  have cardinal := Module.card_eq_pow_finrank (K := ScalarField) (V := Point)
  simp only [ZMod.card] at cardinal
  have lower := point_card_lower_bound
  have upper := point_card_upper_bound
  have small : 2 * baseFieldModulus + 1 < scalarFieldModulus ^ 2 := by decide
  have rank : Module.finrank ScalarField Point = 1 := by
    by_contra other
    have rankTwo : 2 ≤ Module.finrank ScalarField Point := by
      by_contra less
      have zero : Module.finrank ScalarField Point = 0 := by omega
      rw [cardinal, zero, pow_zero] at lower
      have large : 1 < scalarFieldModulus := by decide
      omega
    have powBound : scalarFieldModulus ^ 2 ≤
        scalarFieldModulus ^ Module.finrank ScalarField Point :=
      Nat.pow_le_pow_right (by decide) rankTwo
    rw [← cardinal] at powBound
    omega
  simpa [rank] using cardinal

/-- Each round uses one doubling and at most one point addition. -/
def binaryPointMul [FieldCertificate] : Nat → Nat → Point → Point
  | 0, _, _ => 0
  | rounds + 1, scalar, point =>
      let half := binaryPointMul rounds (scalar / 2) point
      let doubled := half + half
      if scalar % 2 = 1 then doubled + point else doubled

/-- This algorithm counts each group addition that it executes. -/
def binaryPointMulWithCost [FieldCertificate] : Nat → Nat → Point → Point × Nat
  | 0, _, _ => (0, 0)
  | rounds + 1, scalar, point =>
      let half := binaryPointMulWithCost rounds (scalar / 2) point
      let doubled := half.1 + half.1
      if scalar % 2 = 1 then (doubled + point, half.2 + 2)
      else (doubled, half.2 + 1)

/-- The counted algorithm returns the same point and uses at most two additions per round. -/
theorem binaryPointMulWithCost_spec [FieldCertificate] (rounds scalar : Nat) (point : Point) :
    (binaryPointMulWithCost rounds scalar point).1 = binaryPointMul rounds scalar point ∧
      (binaryPointMulWithCost rounds scalar point).2 ≤ 2 * rounds := by
  induction rounds generalizing scalar with
  | zero => simp [binaryPointMulWithCost, binaryPointMul]
  | succ rounds ih =>
      obtain ⟨samePoint, cost⟩ := ih (scalar / 2)
      by_cases odd : scalar % 2 = 1
      all_goals simp only [binaryPointMulWithCost, binaryPointMul, odd,
        ite_true, ite_false, samePoint]
      all_goals constructor
      all_goals first | exact True.intro | omega

/-- This algorithm counts group additions and scalar-loop operations separately.
Each round charges division, remainder, a parity test, and one round step. -/
def binaryPointMulFullCost [FieldCertificate] : Nat → Nat → Point → Point × Nat × Nat
  | 0, _, _ => (0, 0, 0)
  | rounds + 1, scalar, point =>
      let half := binaryPointMulFullCost rounds (scalar / 2) point
      let doubled := half.1 + half.1
      if scalar % 2 = 1 then (doubled + point, half.2.1 + 2, half.2.2 + 4)
      else (doubled, half.2.1 + 1, half.2.2 + 4)

theorem binaryPointMulFullCost_spec [FieldCertificate] (rounds scalar : Nat) (point : Point) :
    (binaryPointMulFullCost rounds scalar point).1 = binaryPointMul rounds scalar point ∧
      (binaryPointMulFullCost rounds scalar point).2.1 ≤ 2 * rounds ∧
      (binaryPointMulFullCost rounds scalar point).2.2 = 4 * rounds := by
  induction rounds generalizing scalar with
  | zero => simp [binaryPointMulFullCost, binaryPointMul]
  | succ rounds ih =>
      obtain ⟨value, additions, operations⟩ := ih (scalar / 2)
      by_cases odd : scalar % 2 = 1
      all_goals simp only [binaryPointMulFullCost, binaryPointMul, odd,
        ite_true, ite_false, value]
      all_goals exact ⟨trivial, by omega, by omega⟩

/-- The bounded binary algorithm computes natural-number multiplication. -/
theorem binaryPointMul_eq [FieldCertificate] (rounds scalar : Nat) (point : Point)
    (bound : scalar < 2 ^ rounds) : binaryPointMul rounds scalar point = scalar • point := by
  induction rounds generalizing scalar with
  | zero =>
      have scalarZero : scalar = 0 := by simpa using bound
      simp [binaryPointMul, scalarZero]
  | succ rounds ih =>
      have halfBound : scalar / 2 < 2 ^ rounds := by
        rw [pow_succ] at bound
        omega
      rw [binaryPointMul, ih _ halfBound]
      have decomp : scalar • point =
          (scalar / 2) • point + (scalar / 2) • point + (scalar % 2) • point := by
        rw [← two_nsmul, ← mul_nsmul, ← add_nsmul]
        congr 1
        omega
      rw [decomp]
      rcases Nat.mod_two_eq_zero_or_one scalar with even | odd
      · simp [even]
      · simp [odd]


/-- This point is the standard BN254 generator `(1,2)`. -/
def standardGenerator [FieldCertificate] : Point :=
  .some 1 2 ((curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mp
    ((equation_iff_onCurve { x := 1, y := 2 }).mpr generatorOnCurve))

private theorem standardGenerator_ne_zero [FieldCertificate] : standardGenerator ≠ 0 := by
  change WeierstrassCurve.Affine.Point.some _ _ _ ≠ .zero
  intro equal; cases equal

/-- Scalar multiplication gives every group point exactly once. -/
theorem scalarGenerator_bijective [FieldCertificate] [GroupCertificate] :
    Function.Bijective (fun scalar : ScalarField => scalar • standardGenerator) := by
  letI : Fact (Nat.Prime scalarFieldModulus) := ⟨scalarFieldPrime⟩
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨smul_left_injective ScalarField standardGenerator_ne_zero,
    (ZMod.card scalarFieldModulus).trans point_card_eq_scalar.symm⟩

/-- One uniform scalar produces the exact uniform point law. -/
theorem scalarGenerator_uniform [FieldCertificate] [GroupCertificate] :
    (PMF.uniformOfFintype ScalarField).map
      (fun scalar => scalar • standardGenerator) = PMF.uniformOfFintype Point :=
  uniform_map_equiv (Equiv.ofBijective _ scalarGenerator_bijective)

/-- This algorithm uses 254 rounds for one scalar. -/
def samplePoint [FieldCertificate] (scalar : ScalarField) : Point :=
  binaryPointMul 254 scalar.val standardGenerator

/-- The point sampler uses at most 508 group additions. -/
theorem samplePoint_groupAdditions [FieldCertificate] (scalar : ScalarField) :
    (binaryPointMulWithCost 254 scalar.val standardGenerator).1 = samplePoint scalar ∧
      (binaryPointMulWithCost 254 scalar.val standardGenerator).2 ≤ 508 := by
  exact binaryPointMulWithCost_spec 254 scalar.val standardGenerator

/-- The bounded algorithm agrees with the certified scalar action. -/
theorem samplePoint_eq_smul [FieldCertificate] [GroupCertificate] (scalar : ScalarField) :
    samplePoint scalar = scalar • standardGenerator := by
  rw [samplePoint, binaryPointMul_eq _ _ _
    (lt_trans scalar.val_lt (show scalarFieldModulus < 2 ^ 254 by decide))]
  have cast : (scalar.val : ScalarField) = scalar := ZMod.natCast_zmod_val scalar
  conv_rhs => rw [← cast, Nat.cast_smul_eq_nsmul]

/-- The bounded algorithm samples the exact uniform point distribution. -/
theorem samplePoint_uniform [FieldCertificate] [GroupCertificate] :
    (PMF.uniformOfFintype ScalarField).map samplePoint = PMF.uniformOfFintype Point := by
  have equal : (samplePoint : ScalarField → Point) =
      (fun scalar => scalar • standardGenerator) := funext samplePoint_eq_smul
  rw [equal]
  exact scalarGenerator_uniform

end Kriterion.ArgoMAC.Security
