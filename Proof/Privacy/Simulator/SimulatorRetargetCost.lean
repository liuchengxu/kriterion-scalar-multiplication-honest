/-
This file counts the arithmetic and element operations in simulator retargeting.
The element counter counts reads and writes separately.
The counters exclude the bookkeeping that records the counts.
-/

import Proof.Privacy.Simulator.PointSampler
import Proof.Privacy.Simulator.ConcreteSimulator

namespace Kriterion.ArgoMAC.Security.SimulatorRetargetCost

open BN254

/-- These counters separate the primitive operations. The field-addition counter includes differences. -/
structure Cost where
  groupAdditions : Nat := 0
  groupNegations : Nat := 0
  fieldAdditions : Nat := 0
  fieldMultiplications : Nat := 0
  fieldDivisions : Nat := 0
  elements : Nat := 0
  scalarOperations : Nat := 0
  deriving DecidableEq

/-- This operation combines the counters of two executed computations. -/
def Cost.add (left right : Cost) : Cost where
  groupAdditions := left.groupAdditions + right.groupAdditions
  groupNegations := left.groupNegations + right.groupNegations
  fieldAdditions := left.fieldAdditions + right.fieldAdditions
  fieldMultiplications := left.fieldMultiplications + right.fieldMultiplications
  fieldDivisions := left.fieldDivisions + right.fieldDivisions
  elements := left.elements + right.elements
  scalarOperations := left.scalarOperations + right.scalarOperations

private theorem binaryScalar_spec [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (point : Point) :
    (binaryPointMulFullCost 254 scalar.val point).1 = scalar • point ∧
      (binaryPointMulFullCost 254 scalar.val point).2.1 ≤ 508 := by
  obtain ⟨same, cost, _⟩ := binaryPointMulFullCost_spec 254 scalar.val point
  refine ⟨same.trans ?_, cost⟩
  rw [binaryPointMul_eq _ _ _
    (lt_trans scalar.val_lt (show scalarFieldModulus < 2 ^ 254 by decide))]
  have cast : (scalar.val : ScalarField) = scalar := ZMod.natCast_zmod_val scalar
  conv_rhs => rw [← cast, Nat.cast_smul_eq_nsmul]

/-- This fold counts one list visit and its binary scalar multiplication per element. -/
def pointHornerWithCost [FieldCertificate] (scalar : ScalarField) :
    List Point → Point × Cost
  | [] => (0, {})
  | point :: points =>
      let tail := pointHornerWithCost scalar points
      let product := binaryPointMulFullCost 254 scalar.val tail.1
      (point + product.1, { tail.2 with
        groupAdditions := tail.2.groupAdditions + product.2.1 + 1
        elements := tail.2.elements + 1
        scalarOperations := tail.2.scalarOperations + product.2.2 })

/-- The counted fold computes the original point polynomial. -/
theorem pointHornerWithCost_value [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (points : List Point) :
    (pointHornerWithCost scalar points).1 = pointHorner scalar points := by
  induction points with
  | nil => rfl
  | cons point points ih =>
      simp only [pointHornerWithCost, pointHorner]
      rw [(binaryScalar_spec scalar _).1, ih]

/-- The fold uses at most 509 group additions per list element. -/
theorem pointHornerWithCost_bound [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (points : List Point) :
    (pointHornerWithCost scalar points).2.groupAdditions ≤ 509 * points.length ∧
      (pointHornerWithCost scalar points).2.elements = points.length ∧
      (pointHornerWithCost scalar points).2.groupNegations = 0 ∧
      (pointHornerWithCost scalar points).2.fieldAdditions = 0 ∧
      (pointHornerWithCost scalar points).2.fieldMultiplications = 0 ∧
      (pointHornerWithCost scalar points).2.fieldDivisions = 0 := by
  induction points with
  | nil => simp [pointHornerWithCost]
  | cons point points ih =>
      have cost := (binaryScalar_spec scalar (pointHornerWithCost scalar points).1).2
      simp only [pointHornerWithCost, List.length_cons]
      rcases ih with ⟨adds, visits, negs, fadds, fmuls, divs⟩
      refine ⟨by omega, by omega, negs, fadds, fmuls, divs⟩

/-- This computation chooses the first output point and keeps the free points. -/
def outputTargetPointsWithCost [FieldCertificate] (point : Point) (free : List Point) :
    List Point × Cost :=
  let tail := pointHornerWithCost radix free
  let product := binaryPointMulFullCost 254 radix.val tail.1
  ((point + -product.1) :: free, { tail.2 with
    groupAdditions := tail.2.groupAdditions + product.2.1 + 1
    groupNegations := tail.2.groupNegations + 1
    elements := tail.2.elements + 1
    scalarOperations := tail.2.scalarOperations + product.2.2 })

/-- The counted point targets agree with the original output construction. -/
theorem outputTargetPointsWithCost_value [FieldCertificate] [GroupCertificate]
    (point : Point) (free : List Point) :
    (outputTargetPointsWithCost point free).1 =
      (point - radix • pointHorner radix free) :: free := by
  simp only [outputTargetPointsWithCost]
  rw [(binaryScalar_spec radix _).1, pointHornerWithCost_value, sub_eq_add_neg]

/-- The point targets use a linear number of group operations and list visits. -/
theorem outputTargetPointsWithCost_bound [FieldCertificate] [GroupCertificate]
    (point : Point) (free : List Point) :
    (outputTargetPointsWithCost point free).2.groupAdditions ≤ 509 * (free.length + 1) ∧
      (outputTargetPointsWithCost point free).2.groupNegations = 1 ∧
      (outputTargetPointsWithCost point free).2.elements = free.length + 1 ∧
      (outputTargetPointsWithCost point free).2.fieldAdditions = 0 ∧
      (outputTargetPointsWithCost point free).2.fieldMultiplications = 0 ∧
      (outputTargetPointsWithCost point free).2.fieldDivisions = 0 := by
  obtain ⟨adds, visits, negs, fadds, fmuls, divs⟩ := pointHornerWithCost_bound radix free
  have cost := (binaryScalar_spec radix (pointHornerWithCost radix free).1).2
  simp only [outputTargetPointsWithCost]
  exact ⟨by omega, by omega, by omega, fadds, fmuls, divs⟩

/-- The homogeneous conversion uses two field multiplications for an affine point. -/
def homogeneousWithCost [FieldCertificate] (point : Point) (scale : NonZeroBase) :
    FieldMacToECMac.HomogeneousValue × Cost :=
  match point with
  | .zero => ({ x := 0, y := scale.value, z := 0 }, {})
  | .some (x := x) (y := y) _ =>
      ({ x := x * scale.value, y := y * scale.value, z := scale.value },
        { fieldMultiplications := 2 })

theorem homogeneousWithCost_value [FieldCertificate] (point : Point) (scale : NonZeroBase) :
    (homogeneousWithCost point scale).1 = homogeneousOfPoint point scale := by
  cases point <;> rfl

theorem homogeneousWithCost_bound [FieldCertificate] (point : Point) (scale : NonZeroBase) :
    (homogeneousWithCost point scale).2.fieldMultiplications ≤ 2 ∧
      (homogeneousWithCost point scale).2.groupAdditions = 0 ∧
      (homogeneousWithCost point scale).2.groupNegations = 0 ∧
      (homogeneousWithCost point scale).2.fieldAdditions = 0 ∧
      (homogeneousWithCost point scale).2.fieldDivisions = 0 ∧
      (homogeneousWithCost point scale).2.elements = 0 := by
  cases point <;> simp [homogeneousWithCost]

/-- This map counts two list reads and one output element per row. -/
def homogeneousRowsWithCost [FieldCertificate] :
    List Point → List NonZeroBase → List FieldMacToECMac.HomogeneousValue × Cost
  | point :: points, scale :: scales =>
      let row := homogeneousWithCost point scale
      let tail := homogeneousRowsWithCost points scales
      (row.1 :: tail.1, { (row.2.add tail.2) with
        elements := row.2.elements + tail.2.elements + 3 })
  | _, _ => ([], {})

theorem homogeneousRowsWithCost_value [FieldCertificate]
    (points : List Point) (scales : List NonZeroBase) :
    (homogeneousRowsWithCost points scales).1 =
      List.zipWith homogeneousOfPoint points scales := by
  induction points generalizing scales with
  | nil => simp [homogeneousRowsWithCost]
  | cons point points ih =>
      cases scales with
      | nil => simp [homogeneousRowsWithCost]
      | cons scale scales =>
          simp [homogeneousRowsWithCost, homogeneousWithCost_value, ih]

theorem homogeneousRowsWithCost_bound [FieldCertificate]
    (points : List Point) (scales : List NonZeroBase)
    (sameLength : points.length = scales.length) :
    (homogeneousRowsWithCost points scales).2.fieldMultiplications ≤ 2 * points.length ∧
      (homogeneousRowsWithCost points scales).2.elements = 3 * points.length ∧
      (homogeneousRowsWithCost points scales).2.groupAdditions = 0 ∧
      (homogeneousRowsWithCost points scales).2.groupNegations = 0 ∧
      (homogeneousRowsWithCost points scales).2.fieldAdditions = 0 ∧
      (homogeneousRowsWithCost points scales).2.fieldDivisions = 0 := by
  induction points generalizing scales with
  | nil => cases scales <;> simp_all [homogeneousRowsWithCost]
  | cons point points ih =>
      cases scales with
      | nil => simp at sameLength
      | cons scale scales =>
          obtain ⟨muls, visits, adds, negs, fadds, divs⟩ := ih scales (by simpa using sameLength)
          obtain ⟨hmuls, hadds, hnegs, hfadds, hdivs, hreads⟩ := homogeneousWithCost_bound point scale
          simp only [homogeneousRowsWithCost, Cost.add, List.length_cons]
          exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

private theorem homogeneousRows_vector [FieldCertificate] {count : Nat}
    (points : Vector Point count) (scales : Vector NonZeroBase count) :
    List.zipWith homogeneousOfPoint points.toList scales.toList =
      (Vector.ofFn fun index => homogeneousOfPoint (points.get index) (scales.get index)).toList := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp
    rfl

/-- This computation returns the output array and counts each conversion pass. -/
def outputTargetsWithCost [FieldCertificate] (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) :
    Array FieldMacToECMac.HomogeneousValue × Cost :=
  let points := outputTargetPointsWithCost point free.toList
  let rows := homogeneousRowsWithCost points.1 scales.toList
  (rows.1.toArray, { (points.2.add rows.2) with
    elements := points.2.elements + rows.2.elements +
      2 * free.size + 2 * scales.size + 2 * rows.1.length })

theorem outputTargetsWithCost_value [FieldCertificate] [GroupCertificate]
    (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) :
    (outputTargetsWithCost point free scales).1 =
      (outputTargets point free scales.get).toArray := by
  apply Array.toList_inj.mp
  simp only [outputTargetsWithCost, List.toList_toArray, homogeneousRowsWithCost_value,
    outputTargetPointsWithCost_value]
  let points : Vector Point FieldMacToECMac.outputMacCount :=
    ⟨((point - radix • pointHorner radix free.toList) :: free.toList).toArray,
      by simp [FieldMacToECMac.outputMacCount]⟩
  exact homogeneousRows_vector points scales

theorem outputTargetsWithCost_bound [FieldCertificate] [GroupCertificate]
    (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) :
    (outputTargetsWithCost point free scales).2.groupAdditions ≤ 46319 ∧
      (outputTargetsWithCost point free scales).2.groupNegations = 1 ∧
      (outputTargetsWithCost point free scales).2.fieldAdditions = 0 ∧
      (outputTargetsWithCost point free scales).2.fieldMultiplications ≤ 182 ∧
      (outputTargetsWithCost point free scales).2.fieldDivisions = 0 ∧
      (outputTargetsWithCost point free scales).2.elements = 908 := by
  have length : (outputTargetPointsWithCost point free.toList).1.length = 91 := by
    rw [outputTargetPointsWithCost_value]
    simp
  obtain ⟨ga, gn, e, fa, fm, fd⟩ := outputTargetPointsWithCost_bound point free.toList
  obtain ⟨hfm, he, hga, hgn, hfa, hfd⟩ := homogeneousRowsWithCost_bound
    (outputTargetPointsWithCost point free.toList).1 scales.toList (by
      simpa [FieldMacToECMac.outputMacCount] using length)
  have rowsLength : (homogeneousRowsWithCost
      (outputTargetPointsWithCost point free.toList).1 scales.toList).1.length = 91 := by
    rw [homogeneousRowsWithCost_value, List.length_zipWith, length]
    simp [FieldMacToECMac.outputMacCount]
  simp only [Vector.length_toList] at ga e
  simp only [length] at hfm he
  simp only [outputTargetsWithCost, Cost.add, Vector.size, rowsLength,
    FieldMacToECMac.outputMacCount]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- The Horner fold executes 254 scalar rounds for each input point. -/
theorem pointHornerWithCost_scalarOperations [FieldCertificate]
    (scalar : ScalarField) (points : List Point) :
    (pointHornerWithCost scalar points).2.scalarOperations = 1016 * points.length := by
  induction points with
  | nil => rfl
  | cons point points ih =>
      have steps := (binaryPointMulFullCost_spec 254 scalar.val
        (pointHornerWithCost scalar points).1).2.2
      simp only [pointHornerWithCost, List.length_cons]
      omega

/-- The target computation executes one additional scalar multiplication. -/
theorem outputTargetPointsWithCost_scalarOperations [FieldCertificate]
    (point : Point) (free : List Point) :
    (outputTargetPointsWithCost point free).2.scalarOperations = 1016 * (free.length + 1) := by
  have tail := pointHornerWithCost_scalarOperations radix free
  have last := (binaryPointMulFullCost_spec 254 radix.val
    (pointHornerWithCost radix free).1).2.2
  simp only [outputTargetPointsWithCost]
  omega

private theorem homogeneousRowsWithCost_scalarOperations [FieldCertificate]
    (points : List Point) (scales : List NonZeroBase) :
    (homogeneousRowsWithCost points scales).2.scalarOperations = 0 := by
  induction points generalizing scales with
  | nil => rfl
  | cons point points ih =>
      cases scales with
      | nil => rfl
      | cons scale scales =>
          simp only [homogeneousRowsWithCost, Cost.add, ih]
          cases point <;> rfl

/-- The complete output-target computation counts all 91 scalar multiplications. -/
theorem outputTargetsWithCost_scalarOperations [FieldCertificate]
    (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) :
    (outputTargetsWithCost point free scales).2.scalarOperations = 92456 := by
  simp only [outputTargetsWithCost, Cost.add, outputTargetPointsWithCost_scalarOperations,
    homogeneousRowsWithCost_scalarOperations, Vector.length_toList]

/-- This fold counts one field multiplication, one field sum, and one list read per bit. -/
def fromBitsWithCost : List BaseField → BaseField × Cost
  | [] => (0, {})
  | value :: values =>
      let tail := fromBitsWithCost values
      (2 * tail.1 + value, { tail.2 with
        fieldAdditions := tail.2.fieldAdditions + 1
        fieldMultiplications := tail.2.fieldMultiplications + 1
        elements := tail.2.elements + 1 })

theorem fromBitsWithCost_value {count : Nat} (values : Fin count → BaseField) :
    (fromBitsWithCost (List.ofFn values)).1 = DigitAdaptor.fromBits values := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.ofFn_succ, fromBitsWithCost, DigitAdaptor.fromBits, Fin.foldr_succ]
      rw [ih]
      rfl

theorem fromBitsWithCost_bound (values : List BaseField) :
    (fromBitsWithCost values).2.fieldAdditions = values.length ∧
      (fromBitsWithCost values).2.fieldMultiplications = values.length ∧
      (fromBitsWithCost values).2.elements = values.length ∧
      (fromBitsWithCost values).2.groupAdditions = 0 ∧
      (fromBitsWithCost values).2.groupNegations = 0 ∧
      (fromBitsWithCost values).2.fieldDivisions = 0 := by
  induction values with
  | nil => simp [fromBitsWithCost]
  | cons value values ih =>
      rcases ih with ⟨adds, muls, visits, gadds, negs, divs⟩
      simp only [fromBitsWithCost, List.length_cons]
      exact ⟨by omega, by omega, by omega, gadds, negs, divs⟩

private theorem vector_toList_ofFn {Value : Type} {count : Nat} (values : Vector Value count) :
    values.toList = List.ofFn values.get := by
  have same : values = Vector.ofFn values.get := by
    apply Vector.ext
    intro index valid
    simp
    rfl
  conv_lhs => rw [same]
  exact Vector.toList_ofFn

/-- This computation changes the first target and copies the remaining target values. -/
def retargetBitsWithCost {count : Nat} (values : Vector BaseField (count + 1))
    (target : BaseField) : Array BaseField × Cost :=
  let free := values.toList.tail
  let weighted := fromBitsWithCost free
  let low := target - 2 * weighted.1
  ((low :: free).toArray, { weighted.2 with
    fieldAdditions := weighted.2.fieldAdditions + 1
    fieldMultiplications := weighted.2.fieldMultiplications + 1
    elements := weighted.2.elements + 2 * values.size + 2 + 2 * (count + 1) })

theorem retargetBitsWithCost_value {count : Nat} (values : Vector BaseField (count + 1))
    (target : BaseField) :
    (retargetBitsWithCost values target).1 =
      (Vector.ofFn (retargetBits values.get target)).toArray := by
  apply Array.toList_inj.mp
  simp only [retargetBitsWithCost, List.toList_toArray]
  rw [vector_toList_ofFn, List.ofFn_succ, List.tail_cons, fromBitsWithCost_value]
  change _ = (Vector.ofFn (retargetBits values.get target)).toList
  rw [Vector.toList_ofFn, List.ofFn_succ]
  rfl

/-- The target adjustment has a linear cost in the number of bits. -/
theorem retargetBitsWithCost_bound {count : Nat} (values : Vector BaseField (count + 1))
    (target : BaseField) :
    (retargetBitsWithCost values target).2.fieldAdditions = count + 1 ∧
      (retargetBitsWithCost values target).2.fieldMultiplications = count + 1 ∧
      (retargetBitsWithCost values target).2.elements = 5 * count + 6 ∧
      (retargetBitsWithCost values target).2.groupAdditions = 0 ∧
      (retargetBitsWithCost values target).2.groupNegations = 0 ∧
      (retargetBitsWithCost values target).2.fieldDivisions = 0 := by
  obtain ⟨adds, muls, visits, gadds, negs, divs⟩ := fromBitsWithCost_bound values.toList.tail
  have length : values.toList.tail.length = count := by simp
  simp only [length] at adds muls visits
  simp only [retargetBitsWithCost, Vector.size]
  exact ⟨by omega, by omega, by omega, gadds, negs, divs⟩

end Kriterion.ArgoMAC.Security.SimulatorRetargetCost
