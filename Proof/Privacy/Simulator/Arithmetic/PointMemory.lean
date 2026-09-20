import Proof.Privacy.Simulator.Arithmetic.Blocks

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each BN254 coordinate fits in one machine word. -/
theorem baseField_word_bound (value : BN254.BaseField) : value.val < 2 ^ 256 := by
  exact lt_trans (ZMod.val_lt value) (by decide : BN254.baseFieldModulus < 2 ^ 256)

/-- A canonical coordinate retains its natural-number value in a machine word. -/
theorem baseField_word_value (value : BN254.BaseField) :
    (BitVec.ofNat 256 value.val).toNat = value.val := by
  exact Nat.mod_eq_of_lt (baseField_word_bound value)

/-- Point reads depend only on their three source registers. -/
theorem readPoint_congr [BN254.FieldCertificate] (first second : Register → Word)
    (source : PointRegisters) (tag : first source.tag = second source.tag)
    (x : first source.x = second source.x) (y : first source.y = second source.y) :
    readPoint first source = readPoint second source := by
  simp only [readPoint, tag, x, y]

/-- Register writes preserve points in disjoint source registers. -/
theorem readPoint_update_other [BN254.FieldCertificate] (registers : Register → Word)
    (source : PointRegisters) (target : Register) (value : Word)
    (tag : source.tag ≠ target) (x : source.x ≠ target) (y : source.y ≠ target) :
    readPoint (Function.update registers target value) source = readPoint registers source := by
  apply readPoint_congr <;> simp_all

/-- Point writes preserve every register outside the target triple. -/
theorem writePoint_other [BN254.FieldCertificate] (registers : Register → Word)
    (target : PointRegisters) (point : BN254.Point) (register : Register)
    (tag : register ≠ target.tag) (x : register ≠ target.x) (y : register ≠ target.y) :
    writePoint registers target point register = registers register := by
  simp only [writePoint, Function.update_of_ne tag, Function.update_of_ne x, Function.update_of_ne y]

/-- The canonical coordinate decoder returns the original nonzero point. -/
theorem decodePoint_coordinates [BN254.FieldCertificate] (x y : BN254.BaseField)
    (valid : BN254.curve.toAffine.Nonsingular x y) :
    BN254.decodePoint ⟨x, y⟩ = some (.some x y valid) := by
  have equation := (BN254.curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
    BN254.discriminantNeZero).mpr valid
  have accepted : BN254.validate ⟨x, y⟩ = true :=
    (BN254.validate_eq_true_iff _).mpr ((BN254.equation_iff_onCurve _).mp equation)
  simp only [BN254.decodePoint, accepted, dif_pos]

/-- Distinct point registers preserve a point through one write and one read. -/
theorem readPoint_writePoint [BN254.FieldCertificate] (registers : Register → Word)
    (target : PointRegisters) (point : BN254.Point)
    (tagX : target.tag ≠ target.x) (tagY : target.tag ≠ target.y) (xy : target.x ≠ target.y) :
    readPoint (writePoint registers target point) target = some point := by
  cases point with
  | zero => simp [readPoint, writePoint, tagX, tagY]; rfl
  | some x y valid =>
      have xBound := ZMod.val_lt x
      have yBound := ZMod.val_lt y
      simp only [readPoint, writePoint, Function.update_of_ne tagY, Function.update_of_ne tagX,
        Function.update_self, Function.update_of_ne xy, baseField_word_value]
      simp only [show (1 : Word) ≠ 0 from by decide, if_false, true_and, and_self,
        xBound, yBound, if_true, ZMod.natCast_zmod_val]
      exact decodePoint_coordinates x y valid

/-- A point-add instruction returns the exact group sum in one charged step. -/
theorem pointAdd_step [BN254.FieldCertificate] (host : Machine) (pc next : Fin (host.size + 1))
    (target left right : PointRegisters) (base : Memory) (a b : BN254.Point)
    (instruction : host.code[pc.val] = .pointAdd target left right next)
    (leftValue : readPoint base.registers left = some a)
    (rightValue : readPoint base.registers right = some b) :
    step host ⟨pc, base⟩ =
      PMF.pure (some (false, ⟨next, {base with registers := writePoint base.registers target (a + b)}⟩)) := by
  simp [step, instruction, leftValue, rightValue]

/-- The point-add prefix preserves stacks and RAM and charges one instruction. -/
theorem pointAdd_prefix [BN254.FieldCertificate] (host : Machine) (pc next : Fin (host.size + 1))
    (target left right : PointRegisters) (base : Memory) (a b : BN254.Point)
    (instruction : host.code[pc.val] = .pointAdd target left right next)
    (leftValue : readPoint base.registers left = some a)
    (rightValue : readPoint base.registers right = some b) :
    runPrefix host 1 ⟨pc, base⟩ = PMF.pure (some (false,
      ⟨next, {base with registers := writePoint base.registers target (a + b)}⟩, 1)) := by
  rw [runPrefix, pointAdd_step host pc next target left right base a b instruction leftValue rightValue]
  simp [runPrefix, PMF.pure_map]

end Kriterion.ArgoMAC.ArithmeticSimulator
