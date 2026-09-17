/-
This file builds the simulator output rows.
-/

import Proof.Privacy.Programming.ProgrammingBridge

namespace Kriterion.ArgoMAC.Security

open BN254

/-- This value represents a point with a nonzero homogeneous scale. -/
def homogeneousOfPoint [FieldCertificate] (point : Point) (scale : NonZeroBase) :
    FieldMacToECMac.HomogeneousValue :=
  match point with
  | .zero => { x := 0, y := scale.value, z := 0 }
  | .some (x := x) (y := y) _ =>
      { x := x * scale.value, y := y * scale.value, z := scale.value }

theorem decodeHomogeneous_homogeneousOfPoint [FieldCertificate]
    (point : Point) (scale : NonZeroBase) :
    Garbling.decodeHomogeneous (homogeneousOfPoint point scale) = some point := by
  induction point with
  | zero =>
      simp [homogeneousOfPoint, Garbling.decodeHomogeneous, scale.nonzero,
        show (0 : Point) = WeierstrassCurve.Affine.Point.zero from rfl]
  | @some x y valid =>
      have onCurve : OnCurve ({ x, y } : AffineInput) :=
        (equation_iff_onCurve _).mp
          ((curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
            discriminantNeZero).mpr valid)
      simp [homogeneousOfPoint, Garbling.decodeHomogeneous, scale.nonzero,
        decodePoint, (validate_eq_true_iff _).mpr onCurve]

/-- The first row fixes the output. The other rows use the free point sample. -/
def outputTargets [FieldCertificate] [GroupCertificate]
    (point : Point) (free : Vector Point 90)
    (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    Vector FieldMacToECMac.HomogeneousValue FieldMacToECMac.outputMacCount :=
  let points : Vector Point FieldMacToECMac.outputMacCount :=
    ⟨((point - radix • pointHorner radix free.toList) :: free.toList).toArray,
      by simp [FieldMacToECMac.outputMacCount]⟩
  Vector.ofFn fun index => homogeneousOfPoint (points.get index) (scales index)

theorem decodePointMacs_outputTargets [FieldCertificate] [GroupCertificate]
    (point : Point) (free : Vector Point 90)
    (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    Garbling.decodePointMacs (outputTargets point free scales) =
      some ((point - radix • pointHorner radix free.toList) :: free.toList) := by
  have decode {count : Nat} (points : Vector Point count)
      (scales : Fin count → NonZeroBase) :
      (Vector.ofFn fun index => homogeneousOfPoint (points.get index) (scales index)).toList.mapM
        Garbling.decodeHomogeneous = some points.toList := by
    rw [Vector.toList_ofFn, List.ofFn_comp' (fun index : Fin count => index)
      (fun index => homogeneousOfPoint (points.get index) (scales index)), List.mapM_map]
    simp only [Function.comp_def, decodeHomogeneous_homogeneousOfPoint]
    change List.mapM (fun index => pure (points.get index)) _ = _
    rw [List.mapM_pure, List.map_ofFn]
    congr 1
    rw [← Vector.toList_ofFn]
    congr 1
    apply Vector.ext
    intro index inRange
    simp only [Vector.getElem_ofFn]
    rfl
  exact decode
    ⟨((point - radix • pointHorner radix free.toList) :: free.toList).toArray,
      by simp [FieldMacToECMac.outputMacCount]⟩ scales

/-- The simulator rows decode to the requested output for every free sample. -/
theorem decodeResult_outputTargets [FieldCertificate] [GroupCertificate]
    (input : AffineInput) (point : Point) (free : Vector Point 90)
    (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    Garbling.decodeResult { point := input, pointMacs := outputTargets point free scales } =
      some point := by
  rw [Garbling.decodeResult, decodePointMacs_outputTargets]
  simp [pointHorner]

@[simp] theorem retargetPointGateRequests_table
    (requests : PointGateRequests) (input : AffineInput)
    (targets : Vector FieldMacToECMac.HomogeneousValue
      FieldMacToECMac.outputMacCount) :
    pointGateTable (retargetPointGateRequests requests input targets) =
      pointGateTable requests := by
  have row (output : Fin FieldMacToECMac.outputMacCount) :=
    retargetPointGateRequests_table_get requests input targets output
  have x : (Vector.ofFn fun output =>
      ((retargetPointGateRequests requests input targets).get output).table.x) =
      Vector.ofFn fun output => (requests.get output).table.x := by
    apply Vector.ext
    intro index inRange
    simpa only [Vector.getElem_ofFn] using congrArg FieldMacToECMac.RowTable.x
      (row ⟨index, inRange⟩)
  have y : (Vector.ofFn fun output =>
      ((retargetPointGateRequests requests input targets).get output).table.y) =
      Vector.ofFn fun output => (requests.get output).table.y := by
    apply Vector.ext
    intro index inRange
    simpa only [Vector.getElem_ofFn] using congrArg FieldMacToECMac.RowTable.y
      (row ⟨index, inRange⟩)
  have z : (Vector.ofFn fun output =>
      ((retargetPointGateRequests requests input targets).get output).table.z) =
      Vector.ofFn fun output => (requests.get output).table.z := by
    apply Vector.ext
    intro index inRange
    simpa only [Vector.getElem_ofFn] using congrArg FieldMacToECMac.RowTable.z
      (row ⟨index, inRange⟩)
  simp only [pointGateTable]
  rw [x, y, z]

theorem retargetedPointGateResults_eq_outputTargets [FieldCertificate] [GroupCertificate]
    (requests : PointGateRequests) (input : AffineInput) (point : Point)
    (free : Vector Point 90) (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    pointGateResults
      (retargetPointGateRequests requests input (outputTargets point free scales)) input =
      outputTargets point free scales := by
  apply Vector.ext
  intro index inRange
  exact retargetPointGateRequests_result_get requests input (outputTargets point free scales)
    ⟨index, inRange⟩

/-- Retargeted point rows decode to the requested simulator output. -/
theorem decodeResult_retargetPointGateResults [FieldCertificate] [GroupCertificate]
    (requests : PointGateRequests) (input : AffineInput) (point : Point)
    (free : Vector Point 90) (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    Garbling.decodeResult {
      point := input
      pointMacs := pointGateResults
        (retargetPointGateRequests requests input (outputTargets point free scales)) input
    } = some point := by
  rw [retargetedPointGateResults_eq_outputTargets]
  exact decodeResult_outputTargets input point free scales

end Kriterion.ArgoMAC.Security
