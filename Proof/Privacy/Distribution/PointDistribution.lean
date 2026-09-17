import Construction.ArgoMAC.RandomizedEncoding
import Cryptography.Primitives
import Proof.Shared.ScalarPrime
import Mathlib.GroupTheory.OrderOfElement

namespace Kriterion.ArgoMAC.Security

open BN254

noncomputable section

instance pointFintype [FieldCertificate] : Fintype Point :=
  Fintype.ofInjective
    (fun point : Point => match point with
      | .zero => (none : Option (BaseField × BaseField))
      | .some (x := x) (y := y) _ => some (x, y)) (by
        intro first second equal
        cases first <;> cases second <;> simp_all)

/-- This equivalence identifies the free offset tape with 90 independent points. -/
def offsetFunctionEquiv [FieldCertificate] : (Fin 90 → Point) ≃ OffsetRandomness where
  toFun values := ⟨List.ofFn values, List.length_ofFn⟩
  invFun values index := values.freeOffsets.get ⟨index.val, by rw [values.freeOffsetCount]; exact index.isLt⟩
  left_inv values := by funext index; exact List.get_ofFn values _
  right_inv values := by
    cases values with
    | mk offsets count =>
      simp only [OffsetRandomness.mk.injEq]
      simpa [count, Fin.cast] using List.ofFn_get offsets

instance offsetRandomnessFintype [FieldCertificate] : Fintype OffsetRandomness :=
  Fintype.ofEquiv (Fin 90 → Point) offsetFunctionEquiv

instance offsetRandomnessNonempty [FieldCertificate] : Nonempty OffsetRandomness :=
  ⟨offsetFunctionEquiv (fun _ => 0)⟩

/-- An equivalence preserves finite uniform mass. -/
theorem uniform_map_equiv {Source Target : Type*}
    [Fintype Source] [Nonempty Source] [Fintype Target] [Nonempty Target]
    (equivalence : Source ≃ Target) :
    (PMF.uniformOfFintype Source).map equivalence = PMF.uniformOfFintype Target :=
  PMF.uniformOfFintype_map_of_bijective equivalence equivalence.bijective

/-- The first coordinate of a uniform product is uniform. -/
theorem uniform_map_fst {First Second : Type*}
    [Fintype First] [Nonempty First] [Fintype Second] [Nonempty Second] :
    (PMF.uniformOfFintype (First × Second)).map Prod.fst = PMF.uniformOfFintype First := by
  classical
  apply PMF.ext
  intro output
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod]
  rw [ENNReal.tsum_prod']
  push_cast
  rw [ENNReal.mul_inv] <;> try simp [Fintype.card_ne_zero]
  rw [mul_left_comm, ENNReal.mul_inv_cancel]
  · simp
  · exact_mod_cast Fintype.card_ne_zero
  · simp

/-- Each coordinate of a uniform point vector is uniform. -/
theorem map_uniform_point_eval [FieldCertificate] {Index : Type*}
    [Fintype Index] [DecidableEq Index] (index : Index) :
    (PMF.uniformOfFintype (Index → Point)).map (fun values => values index) =
      PMF.uniformOfFintype Point := by
  classical
  have h := congrArg (fun p => p.map Prod.fst)
    (uniform_map_equiv (Equiv.piSplitAt index (fun _ => Point)))
  simpa only [PMF.map_comp, uniform_map_fst, Function.comp_def, Equiv.piSplitAt_apply] using h

/-- This equivalence separates a point total from its free coordinates. -/
def pointHornerSplitEquiv [FieldCertificate] [GroupCertificate]
    (count : Nat) (beta : ScalarField) :
    (Fin (count + 1) → Point) ≃ Point × (Fin count → Point) where
  toFun values := (pointHorner beta (List.ofFn values), fun index => values index.succ)
  invFun pair := Fin.cases (pair.1 - beta • pointHorner beta (List.ofFn pair.2)) pair.2
  left_inv values := by
    funext index
    refine Fin.cases ?_ (fun _ => rfl) index
    simp only [Fin.cases_zero, List.ofFn_succ, pointHorner, add_sub_cancel_right]
  right_inv pair := by
    apply Prod.ext
    · simp only [List.ofFn_succ, Fin.cases_zero, Fin.cases_succ, pointHorner,
        sub_add_cancel]
    · rfl

/-- A nonempty uniform point vector has a uniform Horner total. -/
theorem map_uniform_pointHorner [FieldCertificate] [GroupCertificate]
    (count : Nat) (beta : ScalarField) :
    (PMF.uniformOfFintype (Fin (count + 1) → Point)).map
        (fun values => pointHorner beta (List.ofFn values)) = PMF.uniformOfFintype Point := by
  have h := congrArg (fun p => p.map Prod.fst)
    (uniform_map_equiv (pointHornerSplitEquiv count beta))
  simpa only [PMF.map_comp, uniform_map_fst, Function.comp_def, pointHornerSplitEquiv, Equiv.coe_fn_mk] using h

/-- The radix acts as a permutation of the point group. -/
theorem radix_isUnit : IsUnit radix := by
  rw [← ZMod.natCast_zmod_val radix, ZMod.isUnit_iff_coprime]
  decide +kernel

/-- The clamped first offset of a uniform free tape is uniform. -/
theorem map_uniform_clampedPoint [FieldCertificate] [GroupCertificate] (count : Nat) :
    (PMF.uniformOfFintype (Fin (count + 1) → Point)).map
        (fun values => -(radix • pointHorner radix (List.ofFn values))) =
      PMF.uniformOfFintype Point := by
  have h := uniform_map_equiv
    ((MulAction.toPerm (β := Point) radix_isUnit.unit).trans (Equiv.neg Point))
  simp only [Equiv.coe_trans, Function.comp_def, Equiv.neg_apply,
    MulAction.toPerm_apply, Units.smul_def, radix_isUnit.unit_spec] at h
  change (PMF.uniformOfFintype (Fin (count + 1) → Point)).map
    ((fun point => -(radix • point)) ∘ fun values => pointHorner radix (List.ofFn values)) = _
  rw [← PMF.map_comp, map_uniform_pointHorner]
  exact h

/-- The identity event has one point of mass under a uniform point image. -/
theorem uniform_point_zero_mass [FieldCertificate] {Sample : Type*}
    (tape : PMF Sample) (output : Sample → Point)
    (uniform : tape.map output = PMF.uniformOfFintype Point) :
    tape.toOuterMeasure {sample | output sample = 0} = (Fintype.card Point : ENNReal)⁻¹ := by
  have h := congrArg (fun p : PMF Point => p.toOuterMeasure {0}) uniform
  change (tape.map output).toOuterMeasure {0} =
    (PMF.uniformOfFintype Point).toOuterMeasure {0} at h
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton,
    PMF.uniformOfFintype_apply] at h
  exact h

/-- Each offset identity event contributes at most one point of uniform mass. -/
theorem uniform_clampOffsets_identity_mass_le [FieldCertificate] [GroupCertificate]
    (count : Nat) :
    (PMF.uniformOfFintype (Fin (count + 1) → Point)).toOuterMeasure
        {values | (0 : Point) ∈ clampOffsets radix (List.ofFn values)} ≤
      (count + 2 : Nat) / (Fintype.card Point : ENNReal) := by
  classical
  let tape := PMF.uniformOfFintype (Fin (count + 1) → Point)
  let first : Set (Fin (count + 1) → Point) :=
    {values | -(radix • pointHorner radix (List.ofFn values)) = 0}
  let free (index : Fin (count + 1)) : Set (Fin (count + 1) → Point) :=
    {values | values index = 0}
  have firstMass : tape.toOuterMeasure first = (Fintype.card Point : ENNReal)⁻¹ :=
    uniform_point_zero_mass _ _ (map_uniform_clampedPoint count)
  have freeMass (index : Fin (count + 1)) :
      tape.toOuterMeasure (free index) = (Fintype.card Point : ENNReal)⁻¹ :=
    uniform_point_zero_mass _ _ (map_uniform_point_eval index)
  have event : {values : Fin (count + 1) → Point |
      (0 : Point) ∈ clampOffsets radix (List.ofFn values)} = first ∪ ⋃ index, free index := by
    ext values
    simp only [first, free, Set.mem_setOf_eq, clampOffsets, List.mem_cons,
      List.mem_ofFn, Set.mem_union, Set.mem_iUnion]
    exact or_congr eq_comm Iff.rfl
  rw [event]
  calc
    _ ≤ tape.toOuterMeasure first + tape.toOuterMeasure (⋃ index, free index) :=
      MeasureTheory.measure_union_le _ _
    _ ≤ tape.toOuterMeasure first + ∑ index, tape.toOuterMeasure (free index) :=
      add_le_add le_rfl (MeasureTheory.measure_iUnion_fintype_le _ _)
    _ = (count + 2 : Nat) / (Fintype.card Point : ENNReal) := by
      simp only [firstMass, freeMass, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, div_eq_mul_inv]
      ring

/-- The real affine-offset restriction rejects at most 91 points of uniform mass. -/
theorem uniform_offsets_identity_mass_le [FieldCertificate] [GroupCertificate]
    (construction : Construction) :
    (PMF.uniformOfFintype OffsetRandomness).toOuterMeasure
        {randomness | (0 : Point) ∈ construction.offsets randomness} ≤
      91 / (Fintype.card Point : ENNReal) := by
  rw [← uniform_map_equiv offsetFunctionEquiv, PMF.toOuterMeasure_map_apply]
  exact uniform_clampOffsets_identity_mass_le 89

/-- Point translation preserves the uniform mask distribution. -/
theorem map_uniform_point_add [FieldCertificate] (shift : Point) :
    (PMF.uniformOfFintype Point).map (fun point => shift + point) =
      PMF.uniformOfFintype Point :=
  uniform_map_equiv (Equiv.addLeft shift)

/-- The GC1 change of offsets gives exact equality of uniform output distributions. -/
theorem uniform_outputs_eq_simulatedOutputs [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] (construction : Construction) (scalar : ScalarField) (point : Point) :
    (PMF.uniformOfFintype OffsetRandomness).map
        (fun randomness => construction.outputs scalar randomness point) =
      (PMF.uniformOfFintype OffsetRandomness).map
        (construction.simulatedOutputs (scalarMultiplication scalar point)) := by
  conv_lhs => arg 1; ext randomness; rw [construction.outputs_eq_simulatedOutputs_reindex]
  change (PMF.uniformOfFintype OffsetRandomness).map
    (construction.simulatedOutputs (scalarMultiplication scalar point) ∘
      construction.offsetEquiv scalar point) = _
  rw [← PMF.map_comp, uniform_map_equiv]

/-- The generator order gives a lower bound on the point count. -/
theorem point_card_lower_bound [FieldCertificate] [GroupCertificate] :
    scalarFieldModulus ≤ Fintype.card Point := by
  let generator : Point := .some 1 2
    ((curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mp
      ((equation_iff_onCurve { x := 1, y := 2 }).mpr generatorOnCurve))
  have nonzero : generator ≠ 0 := by
    change WeierstrassCurve.Affine.Point.some _ _ _ ≠ .zero
    intro equal
    cases equal
  haveI : Fact (Nat.Prime scalarFieldModulus) := ⟨scalarFieldPrime⟩
  have order := addOrderOf_eq_prime (GroupCertificate.groupOrder generator) nonzero
  rw [← order]
  exact addOrderOf_le_card_univ

/-- The affine-offset restriction has failure mass at most 2^-240. -/
theorem uniform_offsets_identity_mass_le_240bits [FieldCertificate] [GroupCertificate]
    (construction : Construction) :
    (PMF.uniformOfFintype OffsetRandomness).toOuterMeasure
        {randomness | (0 : Point) ∈ construction.offsets randomness} ≤
      (2 : ENNReal) ^ (-240 : ℤ) := by
  calc
    _ ≤ 91 / (Fintype.card Point : ENNReal) := uniform_offsets_identity_mass_le construction
    _ ≤ 91 / (scalarFieldModulus : ENNReal) :=
      ENNReal.div_le_div_left (by exact_mod_cast point_card_lower_bound) _
    _ ≤ (2 : ENNReal) ^ (-240 : ℤ) := by
      rw [ENNReal.zpow_neg, zpow_ofNat, ENNReal.le_inv_iff_mul_le, ← ENNReal.mul_div_right_comm,
        ENNReal.div_le_iff (by norm_num [scalarFieldModulus]) (by simp)]
      norm_num [scalarFieldModulus]

end

end Kriterion.ArgoMAC.Security
