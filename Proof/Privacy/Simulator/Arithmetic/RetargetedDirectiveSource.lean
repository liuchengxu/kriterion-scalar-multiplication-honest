import Proof.Privacy.Simulator.Arithmetic.RetargetCurveGateWords
import Proof.Privacy.Programming.ActualScheduleRecords

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Security

/-- The typed curve directive selects the compiler's exact bit, label, table, target, and lift. -/
theorem curveRetargetedDirective_fields (sample : CurvePublicSample) (input : AffineInput)
    (target : BaseField) (mac : InputMac) (gate : Fin 5) (bit : Fin 254) :
    let directive := (sample.request.retarget input target).actualDirective input mac gate bit
    directive.location = .curve (match gate.val with | 0 => .x3 | 1 => .x5 | 2 => .x7 | 3 => .y4 | _ => .y6) ∧
    directive.window = bit.val ∧
    directive.bit = (if gate.val < 3 then coordinateValues input.x bit else coordinateValues input.y bit) ∧
    directive.label = (if gate.val < 3 then mac.x.get bit else mac.y.get bit) ∧
    directive.table = (sample.tables gate).get bit ∧
    directive.target = (if gate = 2 ∧ bit = 0 then (sample.request.retarget input target).x7Targets 0
      else sample.targets gate bit) ∧
    directive.lift = goodHashLift directive.target (sample.quotients gate bit) := by
  fin_cases gate <;> cases bit using Fin.cases <;>
    simp [CurveGateRequest.actualDirective, CurveGateRequest.retarget,
      CurvePublicSample.request, actualDigitDirective, retargetBits]

/-- The typed x directive selects the compiler's exact bit, label, table, target, and lift. -/
theorem xRetargetedDirective_fields (sample : XPublicSample) (input : AffineInput)
    (target : BaseField) (mac : InputMac) (row : Fin FieldMacToECMac.outputMacCount) (gate : Fin 4) (bit : Fin 254) :
    let directive := (sample.request.retarget input target).actualDirective row input mac gate bit
    directive.location = .point row .x (match gate.val with | 0 => .y6 | 1 => .y8 | 2 => .y10 | _ => .x9) ∧
    directive.window = bit.val ∧
    directive.bit = (if gate.val = 3 then coordinateValues input.x bit else coordinateValues input.y bit) ∧
    directive.label = (if gate.val = 3 then mac.x.get bit else mac.y.get bit) ∧
    directive.table = (sample.tables gate).get bit ∧
    directive.target = (if gate = 3 ∧ bit = 0 then (sample.request.retarget input target).x9Targets 0
      else sample.targets gate bit) ∧
    directive.lift = goodHashLift directive.target (sample.quotients gate bit) := by
  fin_cases gate <;> cases bit using Fin.cases <;>
    simp [BiquadraticXRequest.actualDirective, BiquadraticXRequest.retarget,
      XPublicSample.request, actualDigitDirective, retargetBits]

/-- The typed y directive selects the compiler's exact bit, label, table, target, and lift.
The y row has three adaptors (y6, x7, x9) and retargets its last one. -/
theorem yRetargetedDirective_fields (sample : YPublicSample) (input : AffineInput)
    (target : BaseField) (mac : InputMac) (row : Fin FieldMacToECMac.outputMacCount) (gate : Fin 3) (bit : Fin 254) :
    let directive := (sample.request.retarget input target).actualDirective row input mac gate bit
    directive.location = .point row .y (match gate.val with | 0 => .y6 | 1 => .x7 | _ => .x9) ∧
    directive.window = bit.val ∧
    directive.bit = coordinateValues input.x bit ∧
    directive.label = mac.x.get bit ∧
    directive.table = (sample.tables gate).get bit ∧
    directive.target = (if gate = 2 ∧ bit = 0 then (sample.request.retarget input target).x9Targets 0
      else sample.targets gate bit) ∧
    directive.lift = goodHashLift directive.target (sample.quotients gate bit) := by
  fin_cases gate <;> cases bit using Fin.cases <;>
    simp [BiquadraticYRequest.actualDirective, BiquadraticYRequest.retarget,
      YPublicSample.request, actualDigitDirective, retargetBits]

/-- The typed z directive selects the compiler's exact bit, label, table, target, and lift. -/
theorem zRetargetedDirective_fields (sample : ZPublicSample) (input : AffineInput)
    (target : BaseField) (mac : InputMac) (row : Fin FieldMacToECMac.outputMacCount) (gate : Fin 5) (bit : Fin 254) :
    let directive := (sample.request.retarget input target).actualDirective row input mac gate bit
    directive.location = .point row .z (match gate.val with | 0 => .y6 | 1 => .y8 | 2 => .y10 | 3 => .x7 | _ => .x9) ∧
    directive.window = bit.val ∧
    directive.bit = (if 3 ≤ gate.val then coordinateValues input.x bit else coordinateValues input.y bit) ∧
    directive.label = (if 3 ≤ gate.val then mac.x.get bit else mac.y.get bit) ∧
    directive.table = (sample.tables gate).get bit ∧
    directive.target = (if gate = 4 ∧ bit = 0 then (sample.request.retarget input target).x9Targets 0
      else sample.targets gate bit) ∧
    directive.lift = goodHashLift directive.target (sample.quotients gate bit) := by
  fin_cases gate <;> cases bit using Fin.cases <;>
    simp [BiquadraticZRequest.actualDirective, BiquadraticZRequest.retarget,
      ZPublicSample.request, actualDigitDirective, retargetBits]

end Kriterion.ArgoMAC.ArithmeticSimulator
