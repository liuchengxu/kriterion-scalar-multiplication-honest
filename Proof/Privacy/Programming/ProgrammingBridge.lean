/-
This file builds the selected-row programming bridge.
The bridge keeps the public table and changes only selected oracle points.
-/

import Proof.Privacy.Programming.Gate

namespace Kriterion.ArgoMAC.Security

open BN254

/-- This function changes the low target and keeps every free target. -/
def retargetBits {count : Nat} (values : Fin (count + 1) → BaseField)
    (target : BaseField) : Fin (count + 1) → BaseField :=
  Fin.cases (target - 2 * DigitAdaptor.fromBits (fun index => values index.succ))
    (fun index => values index.succ)

theorem fromBits_retargetBits {count : Nat}
    (values : Fin (count + 1) → BaseField) (target : BaseField) :
    DigitAdaptor.fromBits (retargetBits values target) = target := by
  rw [DigitAdaptor.fromBits, Fin.foldr_succ]
  simp [retargetBits, DigitAdaptor.fromBits]

/-- This request changes one target and keeps the public table and free targets. -/
def CurveGateRequest.retarget (request : CurveGateRequest)
    (input : AffineInput) (target : BaseField) : CurveGateRequest :=
  let residual := target - request.result input + DigitAdaptor.fromBits request.x7Targets
  { request with
    x7Targets := retargetBits request.x7Targets residual
    x7Lifts := fun index => goodHashLift
      (retargetBits request.x7Targets residual index) (request.x7Quotients index)
  }

@[simp] theorem CurveGateRequest.retarget_table (request : CurveGateRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).table = request.table := rfl

@[simp] theorem CurveGateRequest.retarget_result (request : CurveGateRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).result input = target := by
  simp only [CurveGateRequest.retarget, CurveGateRequest.result,
    fromBits_retargetBits]
  ring

/-- This request changes one target and keeps the public table and free targets. -/
def BiquadraticXRequest.retarget (request : BiquadraticXRequest)
    (input : AffineInput) (target : BaseField) : BiquadraticXRequest :=
  let residual := target - request.result input + DigitAdaptor.fromBits request.x9Targets
  { request with
    x9Targets := retargetBits request.x9Targets residual
    x9Lifts := fun index => goodHashLift
      (retargetBits request.x9Targets residual index) (request.x9Quotients index)
  }

@[simp] theorem BiquadraticXRequest.retarget_table (request : BiquadraticXRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).table = request.table := rfl

@[simp] theorem BiquadraticXRequest.retarget_result (request : BiquadraticXRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).result input = target := by
  simp only [BiquadraticXRequest.retarget, BiquadraticXRequest.result,
    fromBits_retargetBits]
  ring

/-- This request changes one target and keeps the public table and free targets. -/
def BiquadraticYRequest.retarget (request : BiquadraticYRequest)
    (input : AffineInput) (target : BaseField) : BiquadraticYRequest :=
  let residual := target - request.result input + DigitAdaptor.fromBits request.x9Targets
  { request with
    x9Targets := retargetBits request.x9Targets residual
    x9Lifts := fun index => goodHashLift
      (retargetBits request.x9Targets residual index) (request.x9Quotients index)
  }

@[simp] theorem BiquadraticYRequest.retarget_table (request : BiquadraticYRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).table = request.table := rfl

@[simp] theorem BiquadraticYRequest.retarget_result (request : BiquadraticYRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).result input = target := by
  simp only [BiquadraticYRequest.retarget, BiquadraticYRequest.result,
    fromBits_retargetBits]
  ring

/-- This request changes one target and keeps the public table and free targets. -/
def BiquadraticZRequest.retarget (request : BiquadraticZRequest)
    (input : AffineInput) (target : BaseField) : BiquadraticZRequest :=
  let residual := target - request.result input + DigitAdaptor.fromBits request.x9Targets
  { request with
    x9Targets := retargetBits request.x9Targets residual
    x9Lifts := fun index => goodHashLift
      (retargetBits request.x9Targets residual index) (request.x9Quotients index)
  }

@[simp] theorem BiquadraticZRequest.retarget_table (request : BiquadraticZRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).table = request.table := rfl

@[simp] theorem BiquadraticZRequest.retarget_result (request : BiquadraticZRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).result input = target := by
  simp only [BiquadraticZRequest.retarget, BiquadraticZRequest.result,
    fromBits_retargetBits]
  ring

/-- This request keeps one row table and selects one homogeneous result. -/
def BiquadraticRowRequest.retarget (request : BiquadraticRowRequest)
    (input : AffineInput) (target : FieldMacToECMac.HomogeneousValue) :
    BiquadraticRowRequest := {
  x := request.x.retarget input target.x
  y := request.y.retarget input target.y
  z := request.z.retarget input target.z
}

@[simp] theorem BiquadraticRowRequest.retarget_table
    (request : BiquadraticRowRequest) (input : AffineInput)
    (target : FieldMacToECMac.HomogeneousValue) :
    (request.retarget input target).table = request.table := by
  rfl

@[simp] theorem BiquadraticRowRequest.retarget_result
    (request : BiquadraticRowRequest) (input : AffineInput)
    (target : FieldMacToECMac.HomogeneousValue) :
    (request.retarget input target).result input = target := by
  simp [BiquadraticRowRequest.retarget, BiquadraticRowRequest.result]

/-- These requests keep all row tables and select all homogeneous results. -/
def retargetPointGateRequests (requests : PointGateRequests)
    (input : AffineInput)
    (targets : Vector FieldMacToECMac.HomogeneousValue
      FieldMacToECMac.outputMacCount) : PointGateRequests :=
  Vector.ofFn fun output => (requests.get output).retarget input (targets.get output)

@[simp] theorem retargetPointGateRequests_get (requests : PointGateRequests)
    (input : AffineInput)
    (targets : Vector FieldMacToECMac.HomogeneousValue
      FieldMacToECMac.outputMacCount)
    (output : Fin FieldMacToECMac.outputMacCount) :
    (retargetPointGateRequests requests input targets).get output =
      (requests.get output).retarget input (targets.get output) := by
  rw [retargetPointGateRequests, Vector.get_ofFn]

@[simp] theorem retargetPointGateRequests_result_get (requests : PointGateRequests)
    (input : AffineInput)
    (targets : Vector FieldMacToECMac.HomogeneousValue
      FieldMacToECMac.outputMacCount)
    (output : Fin FieldMacToECMac.outputMacCount) :
    (pointGateResults (retargetPointGateRequests requests input targets) input).get output =
      targets.get output := by
  rw [pointGateResults, Vector.get_ofFn, retargetPointGateRequests_get,
    BiquadraticRowRequest.retarget_result]

@[simp] theorem retargetPointGateRequests_table_get (requests : PointGateRequests)
    (input : AffineInput)
    (targets : Vector FieldMacToECMac.HomogeneousValue
      FieldMacToECMac.outputMacCount)
    (output : Fin FieldMacToECMac.outputMacCount) :
    ((retargetPointGateRequests requests input targets).get output).table =
      (requests.get output).table := by
  rw [retargetPointGateRequests_get, BiquadraticRowRequest.retarget_table]

/-- Collision-free row programming returns the selected homogeneous value. -/
theorem programRetargetedBiquadraticRow_evaluate
    (state : SimulatorState) (output : Fin FieldMacToECMac.outputMacCount)
    (request : BiquadraticRowRequest) (input : AffineInput)
    (inputMac : InputMac) (target : FieldMacToECMac.HomogeneousValue)
    (invariant : SimulatorInvariant state)
    (notBad : (programGateSchedule state
      ((request.retarget input target).schedule output input inputMac)).bad = false) :
    let final := programGateSchedule state
      ((request.retarget input target).schedule output input inputMac)
    Biquadratic.evaluate (Pipeline.biquadraticOracles final.fixedOracle output .x)
        request.table.x input inputMac = target.x ∧
      Biquadratic.evaluateY (Pipeline.biquadraticOracles final.fixedOracle output .y)
        request.table.y input inputMac = target.y ∧
      Biquadratic.evaluate (Pipeline.biquadraticOracles final.fixedOracle output .z)
        request.table.z input inputMac = target.z := by
  have evaluated := programBiquadraticRowGateSchedule_evaluate state output input inputMac
    (request.retarget input target).x (request.retarget input target).y
    (request.retarget input target).z invariant notBad
  dsimp only at evaluated ⊢
  rcases evaluated with ⟨xValue, yValue, zValue⟩
  constructor
  · simpa only [BiquadraticRowRequest.retarget, BiquadraticRowRequest.schedule, BiquadraticRowRequest.table,
      BiquadraticXRequest.retarget_table,
      BiquadraticXRequest.retarget_result] using xValue
  · constructor
    · simpa only [BiquadraticRowRequest.retarget, BiquadraticRowRequest.schedule, BiquadraticRowRequest.table,
        BiquadraticYRequest.retarget_table,
        BiquadraticYRequest.retarget_result] using yValue
    · simpa only [BiquadraticRowRequest.retarget, BiquadraticRowRequest.schedule, BiquadraticRowRequest.table,
        BiquadraticZRequest.retarget_table,
        BiquadraticZRequest.retarget_result] using zValue

/-- A satisfied retargeted point schedule returns each selected row value. -/
theorem retargetPointGateSchedule_evaluate_get
    (requests : PointGateRequests) (state : SimulatorState)
    (input : AffineInput) (inputMac : InputMac)
    (targets : Vector FieldMacToECMac.HomogeneousValue
      FieldMacToECMac.outputMacCount)
    (satisfied : GateScheduleSatisfied state
      (pointGateSchedule (retargetPointGateRequests requests input targets)
        input inputMac))
    (output : Fin FieldMacToECMac.outputMacCount) :
    (FieldMacToECMac.evaluateHomogeneous
      (pointGateTable (retargetPointGateRequests requests input targets))
      (Pipeline.pointOracles state.fixedOracle) input inputMac).get output =
        targets.get output := by
  have evaluated := pointGateSchedule_evaluate
    (retargetPointGateRequests requests input targets) state input inputMac satisfied
  have selected := congrArg (fun values => values.get output) evaluated
  exact selected.trans (retargetPointGateRequests_result_get requests input targets output)

end Kriterion.ArgoMAC.Security
