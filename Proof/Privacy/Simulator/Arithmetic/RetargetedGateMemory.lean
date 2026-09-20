import Proof.Privacy.Simulator.Arithmetic.RetargetPointGateWords
import Proof.Privacy.Simulator.Arithmetic.RetargetCurveGateWords

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling

/-- The retargeted record retains the exact target, quotient, and table words for every bit gate. -/
structure RetargetedGateMemory {coefficients gates : Nat} (data : GateData coefficients gates)
    (selected : Fin gates) (replacement : BaseField) (ram : Word → Word) (pointer : Word) (start : Nat) : Prop where
  target : ∀ (gate : Fin gates) (bit : Fin 254),
    ram (pointer + BitVec.ofNat 256 (start + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (if gate = selected ∧ bit = 0 then replacement.val else (data.2.2.2 gate bit).val)
  quotient : ∀ (gate : Fin gates) (bit : Fin 254),
    ram (pointer + BitVec.ofNat 256 (start + gates * 254 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (data.2.2.1 gate bit).val
  table : ∀ (gate : Fin gates) (bit : Fin 254),
    ram (pointer + BitVec.ofNat 256 (start + 2 * gates * 254 + 254 * gate.val + bit.val)) =
      ((data.2.1 gate).get bit).trueRow

/-- A read-preserving RAM update retains the complete gate record. -/
theorem RetargetedGateMemory.congr {coefficients gates : Nat} (data : GateData coefficients gates)
    (selected : Fin gates) (replacement : BaseField) (ram next : Word → Word) (pointer : Word) (start : Nat)
    (stored : RetargetedGateMemory data selected replacement ram pointer start)
    (same : ∀ offset, offset < 3 * gates * 254 →
      next (pointer + BitVec.ofNat 256 (start + offset)) = ram (pointer + BitVec.ofNat 256 (start + offset))) :
    RetargetedGateMemory data selected replacement next pointer start := by
  have offsetRead (first : Nat) (bound : first < 3 * gates * 254) := same first bound
  refine ⟨?_, ?_, ?_⟩ <;> intro gate bit
  · have equal := offsetRead (254 * gate.val + bit.val) (by have g := gate.isLt; have b := bit.isLt; omega)
    have value := stored.target gate bit
    simp only [Nat.add_assoc] at equal value ⊢
    exact equal.trans value
  · have equal := offsetRead (gates * 254 + 254 * gate.val + bit.val) (by have g := gate.isLt; have b := bit.isLt; omega)
    have value := stored.quotient gate bit
    simp only [Nat.add_assoc] at equal value ⊢
    exact equal.trans value
  · have equal := offsetRead (2 * gates * 254 + 254 * gate.val + bit.val) (by have g := gate.isLt; have b := bit.isLt; omega)
    have value := stored.table gate bit
    simp only [Nat.add_assoc] at equal value ⊢
    exact equal.trans value

/-- The typed point pass establishes all three gate records in each row. -/
theorem pointRetargetFold_records (sample : Fin FieldMacToECMac.outputMacCount → RowPublicSample) (input : AffineInput)
    (target : Fin FieldMacToECMac.outputMacCount → Fin 3 → BaseField) (pointer : Word) (ram : Word → Word)
    (stored : ∀ row, WordsAt ram pointer (1017 + 9158 * row.val) (rowSchedule.words (sample row))) (row : Fin FieldMacToECMac.outputMacCount) :
    let final := (List.finRange FieldMacToECMac.outputMacCount).foldl
      (fun cells row => pointRowRetargetRam (sample row) input (target row) pointer row cells) ram
    RetargetedGateMemory ((sample row).x.coefficients, (sample row).x.tables, (sample row).x.quotients, (sample row).x.targets)
      3 (((sample row).x.request.retarget input (target row 0)).x9Targets 0) final pointer (1017 + 9158 * row.val + 6105) ∧
    RetargetedGateMemory ((sample row).y.coefficients, (sample row).y.tables, (sample row).y.quotients, (sample row).y.targets)
      2 (((sample row).y.request.retarget input (target row 1)).x9Targets 0) final pointer (1017 + 9158 * row.val + 3815) ∧
    RetargetedGateMemory ((sample row).z.coefficients, (sample row).z.tables, (sample row).z.quotients, (sample row).z.targets)
      4 (((sample row).z.request.retarget input (target row 2)).x9Targets 0) final pointer (1017 + 9158 * row.val) := by
  have x := pointRetargetFold_xData sample input target pointer ram row
  have y := pointRetargetFold_yData sample input target pointer ram row
  have z := pointRetargetFold_zData sample input target pointer ram row
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> intro gate bit
  · exact (x gate bit (stored row)).1
  · exact (x gate bit (stored row)).2.1
  · exact (x gate bit (stored row)).2.2
  · exact (y gate bit (stored row)).1
  · exact (y gate bit (stored row)).2.1
  · exact (y gate bit (stored row)).2.2
  · simpa only [Nat.add_zero] using (z gate bit (stored row)).1
  · simpa only [Nat.add_zero] using (z gate bit (stored row)).2.1
  · simpa only [Nat.add_zero] using (z gate bit (stored row)).2.2

end Kriterion.ArgoMAC.ArithmeticSimulator
