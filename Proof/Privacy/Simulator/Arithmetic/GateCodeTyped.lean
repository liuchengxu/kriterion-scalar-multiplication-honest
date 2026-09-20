import Proof.Privacy.Simulator.Arithmetic.GateTypedData
import Proof.Privacy.Simulator.Arithmetic.GateCodeIndex
import Proof.Privacy.Simulator.Arithmetic.RetargetedDirectiveSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security

/-- Exact source words and coordinate buffers establish one complete typed descriptor. -/
theorem gateCodeAt_typed (location : Pipeline.FixedKeyLocation) (isX : Bool)
    (start gates gate : Nat) (bit : Fin 254) (memory : Memory) (input : AffineInput) (mac : InputMac)
    (directive : GateDirective) (quotient : HashLiftQuotient)
    (coordinates : memory.ram (memory.registers 12) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (memory.registers 12 + 1) = BitVec.ofNat 256 input.y.val)
    (labels : WordsAt memory.ram (memory.registers 14) 0 ((encLinkMacWords mac).map (fun label => label.setWidth 256)))
    (whereGate : directive.location = location) (window : directive.window = bit.val)
    (selected : directive.bit = if isX then coordinateValues input.x bit else coordinateValues input.y bit)
    (label : directive.label = if isX then mac.x.get bit else mac.y.get bit)
    (targetWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 (start + 254 * gate + bit.val)) = BitVec.ofNat 256 directive.target.val)
    (quotientWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 (start + gates * 254 + 254 * gate + bit.val)) = BitVec.ofNat 256 quotient.val)
    (tableWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 (start + 2 * gates * 254 + 254 * gate + bit.val)) = directive.table.trueRow)
    (lift : directive.lift = goodHashLift directive.target quotient) :
    GateTypedData memory (gateCodeAt location isX start gates gate bit) directive quotient := by
  refine ⟨(gateCodeAt_bit location isX start gates gate bit memory input coordinates).trans selected.symm,
    ?_, ?_, targetWord, quotientWord, tableWord, ?_, lift⟩
  · rw [whereGate]
    rfl
  · intro slot
    rw [whereGate, window]
    exact gateCodeAt_index location isX start gates gate bit slot
  · rw [label]
    exact gateCodeAt_label location isX start gates gate bit memory mac labels

/-- The curve descriptor uses the exact selected directive of the retargeted source request. -/
theorem curveGateCode_typed (sample : CurvePublicSample) (input : AffineInput) (target : BaseField)
    (mac : InputMac) (memory : Memory) (gate : Fin 5) (bit : Fin 254)
    (coordinates : memory.ram (memory.registers 12) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (memory.registers 12 + 1) = BitVec.ofNat 256 input.y.val)
    (labels : WordsAt memory.ram (memory.registers 14) 0 ((encLinkMacWords mac).map (fun label => label.setWidth 256)))
    (targetWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 (834395 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (if gate = 2 ∧ bit = 0 then ((sample.request.retarget input target).x7Targets 0).val else (sample.targets gate bit).val))
    (quotientWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 (834395 + 1270 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (sample.quotients gate bit).val)
    (tableWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 (834395 + 2540 + 254 * gate.val + bit.val)) =
      ((sample.tables gate).get bit).trueRow) :
    GateTypedData memory (curveGateCode gate bit)
      ((sample.request.retarget input target).actualDirective input mac gate bit) (sample.quotients gate bit) := by
  let directive := (sample.request.retarget input target).actualDirective input mac gate bit
  rcases curveRetargetedDirective_fields sample input target mac gate bit with
    ⟨whereGate, window, selected, label, table, value, lift⟩
  apply gateCodeAt_typed _ _ _ _ _ bit memory input mac directive (sample.quotients gate bit)
    coordinates labels whereGate window
  · simpa using selected
  · simpa using label
  · rw [value]
    simpa only [apply_ite] using targetWord
  · exact quotientWord
  · rw [table]
    exact tableWord
  · exact lift

/-- The X descriptor uses the exact selected directive of its retargeted source request. -/
theorem xGateCodeAt_typed (sample : XPublicSample) (input : AffineInput) (target : BaseField)
    (mac : InputMac) (memory : Memory) (row : Fin FieldMacToECMac.outputMacCount) (gate : Fin 4) (bit : Fin 254)
    (coordinates : memory.ram (memory.registers 12) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (memory.registers 12 + 1) = BitVec.ofNat 256 input.y.val)
    (labels : WordsAt memory.ram (memory.registers 14) 0 ((encLinkMacWords mac).map (fun label => label.setWidth 256)))
    (targetWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 (1017 + 9158 * row.val + 6105 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (if gate = 3 ∧ bit = 0 then ((sample.request.retarget input target).x9Targets 0).val else (sample.targets gate bit).val))
    (quotientWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 (1017 + 9158 * row.val + 6105 + 1016 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (sample.quotients gate bit).val)
    (tableWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 (1017 + 9158 * row.val + 6105 + 2032 + 254 * gate.val + bit.val)) =
      ((sample.tables gate).get bit).trueRow) :
    GateTypedData memory
      (gateCodeAt (.point row .x (match gate.val with | 0 => .y6 | 1 => .y8 | 2 => .y10 | _ => .x9)) (gate.val = 3) (1017 + 9158 * row.val + 6105) 4 gate.val bit)
      ((sample.request.retarget input target).actualDirective row input mac gate bit) (sample.quotients gate bit) := by
  let directive := (sample.request.retarget input target).actualDirective row input mac gate bit
  rcases xRetargetedDirective_fields sample input target mac row gate bit with
    ⟨whereGate, window, selected, label, table, value, lift⟩
  apply gateCodeAt_typed _ _ _ _ _ bit memory input mac directive (sample.quotients gate bit)
    coordinates labels whereGate window
  · simpa using selected
  · simpa using label
  · rw [value]
    simpa only [apply_ite] using targetWord
  · exact quotientWord
  · rw [table]
    exact tableWord
  · exact lift

/-- The Y descriptor uses the exact selected directive of its retargeted source request.
The y row has three adaptors (y6, x7, x9), all read through the x coordinate. -/
theorem yGateCodeAt_typed (sample : YPublicSample) (input : AffineInput) (target : BaseField)
    (mac : InputMac) (memory : Memory) (row : Fin FieldMacToECMac.outputMacCount) (gate : Fin 3) (bit : Fin 254)
    (coordinates : memory.ram (memory.registers 12) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (memory.registers 12 + 1) = BitVec.ofNat 256 input.y.val)
    (labels : WordsAt memory.ram (memory.registers 14) 0 ((encLinkMacWords mac).map (fun label => label.setWidth 256)))
    (targetWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 (1017 + 9158 * row.val + 3815 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (if gate = 2 ∧ bit = 0 then ((sample.request.retarget input target).x9Targets 0).val else (sample.targets gate bit).val))
    (quotientWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 (1017 + 9158 * row.val + 3815 + 762 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (sample.quotients gate bit).val)
    (tableWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 (1017 + 9158 * row.val + 3815 + 1524 + 254 * gate.val + bit.val)) =
      ((sample.tables gate).get bit).trueRow) :
    GateTypedData memory
      (gateCodeAt (.point row .y (match gate.val with | 0 => .y6 | 1 => .x7 | _ => .x9)) true (1017 + 9158 * row.val + 3815) 3 gate.val bit)
      ((sample.request.retarget input target).actualDirective row input mac gate bit) (sample.quotients gate bit) := by
  let directive := (sample.request.retarget input target).actualDirective row input mac gate bit
  rcases yRetargetedDirective_fields sample input target mac row gate bit with
    ⟨whereGate, window, selected, label, table, value, lift⟩
  apply gateCodeAt_typed _ _ _ _ _ bit memory input mac directive (sample.quotients gate bit)
    coordinates labels whereGate window
  · simpa using selected
  · simpa using label
  · rw [value]
    simpa only [apply_ite] using targetWord
  · exact quotientWord
  · rw [table]
    exact tableWord
  · exact lift

/-- The Z descriptor uses the exact selected directive of its retargeted source request. -/
theorem zGateCodeAt_typed (sample : ZPublicSample) (input : AffineInput) (target : BaseField)
    (mac : InputMac) (memory : Memory) (row : Fin FieldMacToECMac.outputMacCount) (gate : Fin 5) (bit : Fin 254)
    (coordinates : memory.ram (memory.registers 12) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (memory.registers 12 + 1) = BitVec.ofNat 256 input.y.val)
    (labels : WordsAt memory.ram (memory.registers 14) 0 ((encLinkMacWords mac).map (fun label => label.setWidth 256)))
    (targetWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 (1017 + 9158 * row.val + 0 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (if gate = 4 ∧ bit = 0 then ((sample.request.retarget input target).x9Targets 0).val else (sample.targets gate bit).val))
    (quotientWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 (1017 + 9158 * row.val + 0 + 1270 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (sample.quotients gate bit).val)
    (tableWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 (1017 + 9158 * row.val + 0 + 2540 + 254 * gate.val + bit.val)) =
      ((sample.tables gate).get bit).trueRow) :
    GateTypedData memory
      (gateCodeAt (.point row .z (match gate.val with | 0 => .y6 | 1 => .y8 | 2 => .y10 | 3 => .x7 | _ => .x9)) (3 ≤ gate.val) (1017 + 9158 * row.val + 0) 5 gate.val bit)
      ((sample.request.retarget input target).actualDirective row input mac gate bit) (sample.quotients gate bit) := by
  let directive := (sample.request.retarget input target).actualDirective row input mac gate bit
  rcases zRetargetedDirective_fields sample input target mac row gate bit with
    ⟨whereGate, window, selected, label, table, value, lift⟩
  apply gateCodeAt_typed _ _ _ _ _ bit memory input mac directive (sample.quotients gate bit)
    coordinates labels whereGate window
  · simpa using selected
  · simpa using label
  · rw [value]
    simpa only [apply_ite] using targetWord
  · exact quotientWord
  · rw [table]
    exact tableWord
  · exact lift

end Kriterion.ArgoMAC.ArithmeticSimulator
