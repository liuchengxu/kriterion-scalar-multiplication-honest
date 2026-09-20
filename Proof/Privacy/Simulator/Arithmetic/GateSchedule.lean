import Proof.Privacy.Simulator.Arithmetic.GateScheduleCode
import Proof.Privacy.Simulator.Arithmetic.GateLoopBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The curve plan uses the source gate order and increasing coordinate bits. -/
theorem curveGatePlan_get (gate : Fin 5) (bit : Fin 254) :
    curveGatePlan[254 * gate.val + bit.val]'(by have g := gate.isLt; have b := bit.isLt; omega) =
      curveGateCode gate bit := by
  have g := gate.isLt
  have b := bit.isLt
  have quotient : (254 * gate.val + bit.val) / 254 = gate.val := by omega
  have remainder : (254 * gate.val + bit.val) % 254 = bit.val := by omega
  simp only [curveGatePlan, Vector.getElem_ofFn]
  congr 1 <;> exact Fin.ext (by assumption)

/-- The point plan uses increasing rows, source gate order, and increasing coordinate bits. -/
theorem pointGatePlan_get (row : Fin FieldMacToECMac.outputMacCount) (gate : Fin 12) (bit : Fin 254) :
    pointGatePlan[3048 * row.val + 254 * gate.val + bit.val]'(by
      have r := row.isLt; have g := gate.isLt; have b := bit.isLt
      have rowCount : FieldMacToECMac.outputMacCount = 91 := rfl
      omega) = pointGateCode row gate bit := by
  have r := row.isLt
  have g := gate.isLt
  have b := bit.isLt
  have rowValue : (3048 * row.val + 254 * gate.val + bit.val) / 3048 = row.val := by omega
  have gateValue : (3048 * row.val + 254 * gate.val + bit.val) % 3048 / 254 = gate.val := by omega
  have bitValue : (3048 * row.val + 254 * gate.val + bit.val) % 254 = bit.val := by omega
  simp only [pointGatePlan, Vector.getElem_ofFn]
  congr 1 <;> exact Fin.ext (by assumption)

/-- The complete loop budget includes every table entry and its final halt. -/
theorem gateLoop_budget {count : Nat} (plan : Vector GateCode count) (attempts limit : Nat)
    (fits : 1036 * count + 1 < 2 ^ 256) :
    (gateLoop plan attempts fits).size + 1 + (gateDriverRunBudget attempts limit * count + 1) =
      (7722 * attempts + 168 * limit + 1762) * count + 3 := by
  change 1036 * count + 1 + 1 + (gateDriverRunBudget attempts limit * count + 1) = _
  unfold gateDriverRunBudget gateSlotBudget checkedSlotRunBudget
  ring

/-- The two phases contain exactly the paper's 278638 bit gates. -/
theorem gateSchedule_gateCount : curveGatePlan.size + pointGatePlan.size = 278638 := by rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
