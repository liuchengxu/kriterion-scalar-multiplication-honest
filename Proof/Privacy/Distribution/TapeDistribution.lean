import Proof.Privacy.Distribution.HashDistribution
import Construction.ArgoMAC.Seed
import Proof.Privacy.Distribution.PointDistribution

namespace Kriterion.ArgoMAC.Security

open BN254 FieldMacToECMac

noncomputable section

/-- An affine offset decodes to its nonidentity curve point. -/
theorem affineOffset_point_eq [FieldCertificate] (offset : AffineOffset) :
    offset.point = WeierstrassCurve.Affine.Point.some offset.coordinates.x offset.coordinates.y
      ((curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mp
        ((equation_iff_onCurve offset.coordinates).mpr offset.onCurve)) := by
  simp [AffineOffset.point, decodePoint, (validate_eq_true_iff _).mpr offset.onCurve]

/-- Affine offsets are exactly the nonidentity curve points. -/
def affineOffsetEquiv [FieldCertificate] : AffineOffset ≃ {point : Point // point ≠ 0} where
  toFun offset := ⟨offset.point, by rw [affineOffset_point_eq]; intro equal; cases equal⟩
  invFun point := match point with
    | ⟨.zero, nonzero⟩ => False.elim (nonzero rfl)
    | ⟨.some (x := x) (y := y) valid, _⟩ =>
      ⟨⟨x, y⟩, (equation_iff_onCurve _).mp
        ((curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mpr valid)⟩
  left_inv offset := by cases offset; simp [affineOffset_point_eq]
  right_inv point := by
    rcases point with ⟨point, nonzero⟩
    cases point with
    | zero => exact False.elim (nonzero rfl)
    | some valid => apply Subtype.ext; exact affineOffset_point_eq _

theorem affineOffsetEquiv_symm_point [FieldCertificate] (point : {point : Point // point ≠ 0}) :
    (affineOffsetEquiv.symm point).point = point.1 :=
  congrArg Subtype.val (affineOffsetEquiv.apply_symm_apply point)

/-- This type contains the actual successful affine-offset tapes. -/
abbrev ClampedAffineOffsets [FieldCertificate] [GroupCertificate] :=
  {offsets : SuccessfulOffsets // offsets.IsClamped}

/-- This type restricts a point tape to nonidentity offsets. -/
abbrev NonzeroPointOffsets [FieldCertificate] [GroupCertificate] (construction : Construction) :=
  {randomness : OffsetRandomness // (0 : Point) ∉ construction.offsets randomness}

/-- A successful affine tape gives a nonidentity point tape. -/
def clampedPointOffsets [FieldCertificate] [GroupCertificate] (construction : Construction)
    (offsets : ClampedAffineOffsets) : NonzeroPointOffsets construction :=
  ⟨⟨freeOffsetPoints offsets.1.free, by simp [freeOffsetPoints]⟩, by
    simp only [Construction.offsets, clampOffsets, List.mem_cons, not_or]
    constructor
    · change ¬(0 : Point) = clampedFirst offsets.1.free
      rw [← offsets.2]
      exact Ne.symm (affineOffsetEquiv offsets.1.first).2
    · intro member
      obtain ⟨offset, _, equal⟩ := List.mem_map.mp member
      exact (affineOffsetEquiv offset).2 equal⟩

/-- The free affine coordinates determine a successful tape. -/
theorem clampedPointOffsets_injective [FieldCertificate] [GroupCertificate]
    (construction : Construction) : Function.Injective (clampedPointOffsets construction) := by
  intro first second equal
  have freePoints : freeOffsetPoints first.1.free = freeOffsetPoints second.1.free :=
    congrArg (fun value => value.1.freeOffsets) equal
  have free : first.1.free = second.1.free := by
    apply Vector.toList_inj.mp
    exact List.map_injective_iff.mpr (fun a b equal =>
      affineOffsetEquiv.injective (Subtype.ext equal)) freePoints
  have head : first.1.first = second.1.first := by
    apply affineOffsetEquiv.injective
    apply Subtype.ext
    change first.1.first.point = second.1.first.point
    rw [first.2, second.2, free]
  apply Subtype.ext
  rcases first with ⟨⟨first, freeFirst⟩, firstClamped⟩
  rcases second with ⟨⟨second, freeSecond⟩, secondClamped⟩
  simp_all

/-- The free point list determines its length-certified tape. -/
theorem offsetRandomness_ext [FieldCertificate] (a b : OffsetRandomness)
    (equal : a.freeOffsets = b.freeOffsets) : a = b := by
  cases a
  cases b
  cases equal
  rfl

theorem clampedPointOffsets_eq_of_free [FieldCertificate] [GroupCertificate]
    (construction : Construction) (offsets : ClampedAffineOffsets)
    (randomness : NonzeroPointOffsets construction)
    (equal : freeOffsetPoints offsets.1.free = randomness.1.freeOffsets) :
    clampedPointOffsets construction offsets = randomness := by
  apply Subtype.ext
  apply offsetRandomness_ext
  exact equal

def affineFreeFromPoints [FieldCertificate]
    (values : Fin 90 → {point : Point // point ≠ 0}) : Vector AffineOffset 90 :=
  Vector.ofFn fun index => affineOffsetEquiv.symm (values index)

theorem affineFreeFromPoints_eq [FieldCertificate]
    (values : Fin 90 → {point : Point // point ≠ 0}) :
    freeOffsetPoints (affineFreeFromPoints values) = List.ofFn (fun index => (values index).1) := by
  rw [freeOffsetPoints, affineFreeFromPoints, Vector.toList_ofFn, List.map_ofFn]
  apply congrArg List.ofFn
  funext index
  exact affineOffsetEquiv_symm_point (values index)

theorem offsetFunctionEquiv_symm_list [FieldCertificate] (randomness : OffsetRandomness) :
    List.ofFn (offsetFunctionEquiv.symm randomness) = randomness.freeOffsets :=
  congrArg OffsetRandomness.freeOffsets (offsetFunctionEquiv.apply_symm_apply randomness)

theorem exists_clampedPointOffsets_of_free [FieldCertificate] [GroupCertificate]
    (construction : Construction) (randomness : NonzeroPointOffsets construction)
    (free : Vector AffineOffset 90)
    (freeEq : freeOffsetPoints free = randomness.1.freeOffsets) :
    ∃ offsets, clampedPointOffsets construction offsets = randomness := by
  have firstNonzero : clampedFirst free ≠ 0 := by
    intro zero
    apply randomness.2
    simp only [clampedFirst, freeEq] at zero
    simp only [Construction.offsets, clampOffsets, List.mem_cons]
    exact Or.inl zero.symm
  obtain ⟨first, equal⟩ := affineOffsetEquiv.surjective ⟨clampedFirst free, firstNonzero⟩
  have clamped : (SuccessfulOffsets.mk first free).IsClamped :=
    congrArg Subtype.val equal
  refine ⟨⟨⟨first, free⟩, clamped⟩, ?_⟩
  exact clampedPointOffsets_eq_of_free construction _ _ freeEq

theorem exists_clampedPointOffsets_of_list [FieldCertificate] [GroupCertificate]
    (construction : Construction) (randomness : NonzeroPointOffsets construction)
    (values : Fin 90 → Point) (listEq : List.ofFn values = randomness.1.freeOffsets) :
    ∃ offsets, clampedPointOffsets construction offsets = randomness := by
  have nonzero (index : Fin 90) : values index ≠ 0 := by
    intro zero
    apply randomness.2
    simp only [Construction.offsets, clampOffsets, List.mem_cons]
    right
    rw [← listEq, List.mem_ofFn]
    exact ⟨index, zero⟩
  let free := affineFreeFromPoints fun index => ⟨values index, nonzero index⟩
  have freeEq : freeOffsetPoints free = randomness.1.freeOffsets :=
    (affineFreeFromPoints_eq (fun index => ⟨values index, nonzero index⟩)).trans listEq
  exact exists_clampedPointOffsets_of_free construction randomness free freeEq

theorem clampedPointOffsets_surjective [FieldCertificate] [GroupCertificate]
    (construction : Construction) : Function.Surjective (clampedPointOffsets construction) := by
  intro randomness
  exact exists_clampedPointOffsets_of_list construction randomness
    (offsetFunctionEquiv.symm randomness.1) (offsetFunctionEquiv_symm_list randomness.1)

/-- The actual affine restriction is exactly the nonidentity point restriction. -/
def clampedOffsetEquiv [FieldCertificate] [GroupCertificate] (construction : Construction) :
    ClampedAffineOffsets ≃ NonzeroPointOffsets construction :=
  Equiv.ofBijective (clampedPointOffsets construction)
    ⟨clampedPointOffsets_injective construction, clampedPointOffsets_surjective construction⟩

attribute [local instance] affineOffsetFintype successfulOffsetsFintype

instance clampedAffineOffsetsFintype [FieldCertificate] [GroupCertificate] :
    Fintype ClampedAffineOffsets := Fintype.ofFinite _

instance clampedAffineOffsetsNonempty [FieldCertificate] [GroupCertificate] :
    Nonempty ClampedAffineOffsets := ⟨⟨Seed.offsets, Seed.offsets_clamped⟩⟩

instance nonzeroPointOffsetsFintype [FieldCertificate] [GroupCertificate]
    (construction : Construction) : Fintype (NonzeroPointOffsets construction) := Fintype.ofFinite _

instance nonzeroPointOffsetsNonempty [FieldCertificate] [GroupCertificate]
    (construction : Construction) : Nonempty (NonzeroPointOffsets construction) :=
  ⟨clampedPointOffsets construction ⟨Seed.offsets, Seed.offsets_clamped⟩⟩

/-- Uniform successful affine offsets give uniform restricted point offsets. -/
theorem map_uniform_clampedPointOffsets [FieldCertificate] [GroupCertificate]
    (construction : Construction) :
    (PMF.uniformOfFintype ClampedAffineOffsets).map (clampedPointOffsets construction) =
      PMF.uniformOfFintype (NonzeroPointOffsets construction) :=
  uniform_map_equiv (clampedOffsetEquiv construction)

attribute [local instance] vectorFintype rowRandomnessFintype

/-- This type contains every tape value except the offsets. -/
abbrev GarblingOffsetRest :=
  FieldMacToECMac.Randomness × GarblingFieldData × GarblingOracleData

instance garblingOffsetRestNonempty : Nonempty GarblingOffsetRest :=
  ⟨((Seed.randomness 0).pointRandomness,
    (Garbling.Randomness.data (Seed.randomness 0)).algebraic.field, (Garbling.Randomness.data (Seed.randomness 0)).oracles)⟩

/-- The actual tape separates into clamped offsets and independent remaining values. -/
def garblingRandomnessOffsetEquiv [FieldCertificate] [GroupCertificate] :
    Garbling.Randomness ≃ ClampedAffineOffsets × GarblingOffsetRest where
  toFun randomness := (⟨randomness.offsets, randomness.offsetsClamped⟩,
    randomness.pointRandomness, (Garbling.Randomness.data randomness).algebraic.field, (Garbling.Randomness.data randomness).oracles)
  invFun sample := {
    offsets := sample.1.1
    offsetsClamped := sample.1.2
    pointRandomness := sample.2.1
    bridgeKey := sample.2.2.1.bridgeKey
    curveMask := sample.2.2.1.curveMask
    curveR1 := sample.2.2.1.curveR1
    curveR2 := sample.2.2.1.curveR2
    fixedKeyOracle := sample.2.2.2.fixedKeyOracle
    inputMacKey := sample.2.2.2.inputMacKey
    encPRFOracle := sample.2.2.2.encPRFOracle
    hashOracle := sample.2.2.2.hashOracle
  }
  left_inv randomness := by cases randomness; rfl
  right_inv sample := by
    rcases sample with ⟨⟨⟨first, free⟩, clamped⟩, point, field, oracles⟩
    cases field
    cases oracles
    rfl

/-- The actual tape has uniform nonidentity point offsets and independent remaining values. -/
def garblingRandomnessPointEquiv [FieldCertificate] [GroupCertificate]
    (construction : Construction) :
    Garbling.Randomness ≃ NonzeroPointOffsets construction × GarblingOffsetRest :=
  garblingRandomnessOffsetEquiv.trans
    (Equiv.prodCongr (clampedOffsetEquiv construction) (Equiv.refl _))

theorem garblingRandomnessPointEquiv_offsets [FieldCertificate] [GroupCertificate]
    (construction : Construction) (randomness : Garbling.Randomness) :
    construction.offsets (garblingRandomnessPointEquiv construction randomness).1.1 =
      randomness.offsets.values.toList.map AffineOffset.point := by
  change clampOffsets radix (freeOffsetPoints randomness.offsets.free) = _
  simp only [clampOffsets, SuccessfulOffsets.values, Vector.toList_mk,
    List.map_cons]
  rw [randomness.offsetsClamped]
  rfl

theorem map_randomTape_pointSplit [FieldCertificate] [GroupCertificate]
    (construction : Construction) (witness : Garbling.Randomness) (parameter : Nat) :
    (randomTape witness parameter).map (garblingRandomnessPointEquiv construction) =
      PMF.uniformOfFintype (NonzeroPointOffsets construction × GarblingOffsetRest) := by
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  exact uniform_map_equiv (garblingRandomnessPointEquiv construction)

/-- The cardinality loss equals the probability of an identity offset. -/
theorem nonzeroPointOffsets_card_loss [FieldCertificate] [GroupCertificate]
    (construction : Construction) :
    1 - (Fintype.card (NonzeroPointOffsets construction) : ℝ) /
        Fintype.card OffsetRandomness ≤ (2 : ℝ) ^ (-240 : ℤ) := by
  classical
  have bound := ENNReal.toReal_mono (by finiteness)
    (uniform_offsets_identity_mass_le_240bits construction)
  rw [PMF.toOuterMeasure_uniformOfFintype_apply] at bound
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.zpow_neg, zpow_ofNat, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat] at bound
  have card : Fintype.card (NonzeroPointOffsets construction) =
      Fintype.card OffsetRandomness -
        Fintype.card {randomness : OffsetRandomness |
          (0 : Point) ∈ construction.offsets randomness} :=
    @Fintype.card_subtype_compl OffsetRandomness offsetRandomnessFintype (fun randomness =>
      (0 : Point) ∈ construction.offsets randomness)
      (inferInstance : Fintype {randomness : OffsetRandomness |
        (0 : Point) ∈ construction.offsets randomness}) (nonzeroPointOffsetsFintype construction)
  rw [card, Nat.cast_sub (Fintype.card_subtype_le _), sub_div,
    div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  linarith

/-- The restricted tape embeds into the full point tape. -/
def nonzeroPointTapeEmbed [FieldCertificate] [GroupCertificate] (construction : Construction)
    (sample : NonzeroPointOffsets construction × GarblingOffsetRest) :
    OffsetRandomness × GarblingOffsetRest := (sample.1.1, sample.2)

theorem nonzeroPointTapeEmbed_injective [FieldCertificate] [GroupCertificate]
    (construction : Construction) : Function.Injective (nonzeroPointTapeEmbed construction) := by
  intro first second equal
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst equal)
  · exact congrArg (fun sample : OffsetRandomness × GarblingOffsetRest => sample.2) equal

/-- The affine restriction costs at most 2^-240 for every later observation. -/
theorem randomTape_point_observation_bound [FieldCertificate] [GroupCertificate]
    {Observation : Type*} (construction : Construction)
    (witness : Garbling.Randomness) (parameter : Nat)
    (observe : OffsetRandomness × GarblingOffsetRest → PMF Observation)
    (event : Set Observation) :
    |(((PMF.uniformOfFintype (OffsetRandomness × GarblingOffsetRest)).bind observe).toOuterMeasure event).toReal -
      (((randomTape witness parameter).bind (fun randomness =>
        observe (nonzeroPointTapeEmbed construction
          (garblingRandomnessPointEquiv construction randomness)))).toOuterMeasure event).toReal| ≤
      (2 : ℝ) ^ (-240 : ℤ) := by
  have bound := uniformEmbedding_observation_bound (nonzeroPointTapeEmbed construction)
    (nonzeroPointTapeEmbed_injective construction) observe event
  have actual : (randomTape witness parameter).bind (fun randomness =>
      observe (nonzeroPointTapeEmbed construction
        (garblingRandomnessPointEquiv construction randomness))) =
      (PMF.uniformOfFintype (NonzeroPointOffsets construction × GarblingOffsetRest)).bind
        (observe ∘ nonzeroPointTapeEmbed construction) := by
    rw [← map_randomTape_pointSplit construction witness parameter, PMF.bind_map]
    rfl
  rw [actual]
  apply bound.trans
  rw [Fintype.card_prod (α := NonzeroPointOffsets construction) (β := GarblingOffsetRest),
    Fintype.card_prod (α := OffsetRandomness) (β := GarblingOffsetRest),
    Nat.cast_mul, Nat.cast_mul]
  rw [mul_div_mul_right _ _ (show (Fintype.card GarblingOffsetRest : ℝ) ≠ 0 from
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  exact nonzeroPointOffsets_card_loss construction

end

end Kriterion.ArgoMAC.Security
