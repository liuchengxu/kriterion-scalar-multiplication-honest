import Proof.Privacy.Simulator.Arithmetic.RetargetPointPassValues
import Proof.Privacy.Simulator.Arithmetic.GateQuotientLayout

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling

/-- Every unchanged source cell retains its original sampled word. -/
theorem pointRetargetFold_free (sample : Fin FieldMacToECMac.outputMacCount → RowPublicSample) (input : AffineInput)
    (target : Fin FieldMacToECMac.outputMacCount → Fin 3 → BaseField) (pointer : Word) (ram : Word → Word)
    (row : Fin FieldMacToECMac.outputMacCount) (offset : Nat) (inside : offset < 9158)
    (notX : offset ≠ 6867) (notY : offset ≠ 4323) (notZ : offset ≠ 1016) :
    (List.finRange FieldMacToECMac.outputMacCount).foldl
      (fun cells row => pointRowRetargetRam (sample row) input (target row) pointer row cells) ram
      (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + offset)) =
      ram (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + offset)) := by
  apply pointRetargetFold_outside
  intro written member
  have rowCount : FieldMacToECMac.outputMacCount = 91 := rfl
  have firstBound := row.isLt
  have secondBound := written.isLt
  refine ⟨?_, ?_, ?_⟩
  · apply privateOffset_add_ne _ _ _ 762 <;> omega
  · apply privateOffset_add_ne _ _ _ 508 <;> omega
  · apply privateOffset_add_ne _ _ _ 1016 <;> omega

/-- The point pass preserves the curve data and every later private word. -/
theorem pointRetargetFold_afterRows (sample : Fin FieldMacToECMac.outputMacCount → RowPublicSample) (input : AffineInput)
    (target : Fin FieldMacToECMac.outputMacCount → Fin 3 → BaseField) (pointer : Word) (ram : Word → Word)
    (offset : Nat) (afterRows : 834395 ≤ offset) (fits : offset < 2 ^ 256) :
    (List.finRange FieldMacToECMac.outputMacCount).foldl
      (fun cells row => pointRowRetargetRam (sample row) input (target row) pointer row cells) ram
      (pointer + BitVec.ofNat 256 offset) = ram (pointer + BitVec.ofNat 256 offset) := by
  apply pointRetargetFold_outside
  intro written member
  have rowCount : FieldMacToECMac.outputMacCount = 91 := rfl
  have rowBound := written.isLt
  refine ⟨?_, ?_, ?_⟩
  · apply privateOffset_add_ne _ offset _ 762 <;> omega
  · apply privateOffset_add_ne _ offset _ 508 <;> omega
  · apply privateOffset_add_ne _ offset _ 1016 <;> omega

/-- The X descriptors read the exact retargeted targets, original quotients, and original table words. -/
theorem pointRetargetFold_xData (sample : Fin FieldMacToECMac.outputMacCount → RowPublicSample) (input : AffineInput)
    (target : Fin FieldMacToECMac.outputMacCount → Fin 3 → BaseField) (pointer : Word) (ram : Word → Word)
    (row : Fin FieldMacToECMac.outputMacCount) (gate : Fin 4) (bit : Fin 254)
    (stored : WordsAt ram pointer (1017 + 9158 * row.val) (rowSchedule.words (sample row))) :
    let final := (List.finRange FieldMacToECMac.outputMacCount).foldl
      (fun cells row => pointRowRetargetRam (sample row) input (target row) pointer row cells) ram
    final (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 6105 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (if gate = 3 ∧ bit = 0 then
        (((sample row).x.request.retarget input (target row 0)).x9Targets 0).val
        else ((sample row).x.targets gate bit).val) ∧
    final (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 6105 + 1016 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 ((sample row).x.quotients gate bit).val ∧
    final (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 6105 + 2032 + 254 * gate.val + bit.val)) =
      (((sample row).x.tables gate).get bit).trueRow := by
  have gateBound := gate.isLt
  have bitBound := bit.isLt
  have original := row_x_words (sample row) ram pointer (1017 + 9158 * row.val) stored
  have targetWord := gateData_target 5 4 _ ram pointer _ gate bit original
  have quotientWord := gateData_quotient 5 4 _ ram pointer _ gate bit original
  have tableWord := gateData_table 5 4 _ ram pointer _ gate bit original
  simp only [coordinateBitCount, Nat.reduceMul, Nat.add_assoc, Nat.add_zero, Nat.zero_add] at targetWord quotientWord tableWord
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · by_cases selected : gate = 3 ∧ bit = 0
    · rcases selected with ⟨rfl, rfl⟩
      simpa only [show (3 : Fin 4).val = 3 from rfl, show (0 : Fin 254).val = 0 from rfl, ↓reduceIte, Nat.mul_zero, Nat.add_zero, Fin.val_zero, Fin.val_ofNat, Nat.reduceMod,
        Nat.reduceMul, Nat.reduceAdd, Nat.add_assoc, and_self] using
        (pointRetargetFold_values sample input target pointer ram row).1
    · rw [if_neg selected]
      have different : ¬(gate.val = 3 ∧ bit.val = 0) := by
        rintro ⟨first, second⟩
        exact selected ⟨Fin.ext first, Fin.ext second⟩
      have unchanged := pointRetargetFold_free sample input target pointer ram row (6105 + 254 * gate.val + bit.val)
        (by omega) (by omega) (by omega) (by omega)
      simp only [Nat.add_assoc, Nat.add_zero, Nat.zero_add] at unchanged
      simpa only [coordinateBitCount, Nat.add_assoc, Nat.add_zero, Nat.zero_add] using unchanged.trans targetWord
  · have unchanged := pointRetargetFold_free sample input target pointer ram row (6105 + 1016 + 254 * gate.val + bit.val)
      (by omega) (by omega) (by omega) (by omega)
    simp only [Nat.add_assoc, Nat.add_zero, Nat.zero_add] at unchanged
    simpa only [coordinateBitCount, Nat.reduceMul, Nat.add_assoc, Nat.add_zero, Nat.zero_add] using unchanged.trans quotientWord
  · have unchanged := pointRetargetFold_free sample input target pointer ram row (6105 + 2032 + 254 * gate.val + bit.val)
      (by omega) (by omega) (by omega) (by omega)
    simp only [Nat.add_assoc, Nat.add_zero, Nat.zero_add] at unchanged
    simpa only [coordinateBitCount, Nat.reduceMul, Nat.add_assoc, Nat.add_zero, Nat.zero_add] using unchanged.trans tableWord

/-- The Y descriptors read the exact retargeted targets, original quotients, and original table words. -/
theorem pointRetargetFold_yData (sample : Fin FieldMacToECMac.outputMacCount → RowPublicSample) (input : AffineInput)
    (target : Fin FieldMacToECMac.outputMacCount → Fin 3 → BaseField) (pointer : Word) (ram : Word → Word)
    (row : Fin FieldMacToECMac.outputMacCount) (gate : Fin 3) (bit : Fin 254)
    (stored : WordsAt ram pointer (1017 + 9158 * row.val) (rowSchedule.words (sample row))) :
    let final := (List.finRange FieldMacToECMac.outputMacCount).foldl
      (fun cells row => pointRowRetargetRam (sample row) input (target row) pointer row cells) ram
    final (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 3815 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (if gate = 2 ∧ bit = 0 then
        (((sample row).y.request.retarget input (target row 1)).x9Targets 0).val
        else ((sample row).y.targets gate bit).val) ∧
    final (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 3815 + 762 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 ((sample row).y.quotients gate bit).val ∧
    final (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 3815 + 1524 + 254 * gate.val + bit.val)) =
      (((sample row).y.tables gate).get bit).trueRow := by
  have gateBound := gate.isLt
  have bitBound := bit.isLt
  have original := row_y_words (sample row) ram pointer (1017 + 9158 * row.val) stored
  have targetWord := gateData_target 4 3 _ ram pointer _ gate bit original
  have quotientWord := gateData_quotient 4 3 _ ram pointer _ gate bit original
  have tableWord := gateData_table 4 3 _ ram pointer _ gate bit original
  simp only [coordinateBitCount, Nat.reduceMul, Nat.add_assoc, Nat.add_zero, Nat.zero_add] at targetWord quotientWord tableWord
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · by_cases selected : gate = 2 ∧ bit = 0
    · rcases selected with ⟨rfl, rfl⟩
      simpa only [show (2 : Fin 3).val = 2 from rfl, show (0 : Fin 254).val = 0 from rfl, ↓reduceIte, Nat.mul_zero, Nat.add_zero, Fin.val_zero, Fin.val_ofNat, Nat.reduceMod,
        Nat.reduceMul, Nat.reduceAdd, Nat.add_assoc, and_self] using
        (pointRetargetFold_values sample input target pointer ram row).2.1
    · rw [if_neg selected]
      have different : ¬(gate.val = 2 ∧ bit.val = 0) := by
        rintro ⟨first, second⟩
        exact selected ⟨Fin.ext first, Fin.ext second⟩
      have unchanged := pointRetargetFold_free sample input target pointer ram row (3815 + 254 * gate.val + bit.val)
        (by omega) (by omega) (by omega) (by omega)
      simp only [Nat.add_assoc, Nat.add_zero, Nat.zero_add] at unchanged
      simpa only [coordinateBitCount, Nat.add_assoc, Nat.add_zero, Nat.zero_add] using unchanged.trans targetWord
  · have unchanged := pointRetargetFold_free sample input target pointer ram row (3815 + 762 + 254 * gate.val + bit.val)
      (by omega) (by omega) (by omega) (by omega)
    simp only [Nat.add_assoc, Nat.add_zero, Nat.zero_add] at unchanged
    simpa only [coordinateBitCount, Nat.reduceMul, Nat.add_assoc, Nat.add_zero, Nat.zero_add] using unchanged.trans quotientWord
  · have unchanged := pointRetargetFold_free sample input target pointer ram row (3815 + 1524 + 254 * gate.val + bit.val)
      (by omega) (by omega) (by omega) (by omega)
    simp only [Nat.add_assoc, Nat.add_zero, Nat.zero_add] at unchanged
    simpa only [coordinateBitCount, Nat.reduceMul, Nat.add_assoc, Nat.add_zero, Nat.zero_add] using unchanged.trans tableWord

/-- The Z descriptors read the exact retargeted targets, original quotients, and original table words. -/
theorem pointRetargetFold_zData (sample : Fin FieldMacToECMac.outputMacCount → RowPublicSample) (input : AffineInput)
    (target : Fin FieldMacToECMac.outputMacCount → Fin 3 → BaseField) (pointer : Word) (ram : Word → Word)
    (row : Fin FieldMacToECMac.outputMacCount) (gate : Fin 5) (bit : Fin 254)
    (stored : WordsAt ram pointer (1017 + 9158 * row.val) (rowSchedule.words (sample row))) :
    let final := (List.finRange FieldMacToECMac.outputMacCount).foldl
      (fun cells row => pointRowRetargetRam (sample row) input (target row) pointer row cells) ram
    final (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 0 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (if gate = 4 ∧ bit = 0 then
        (((sample row).z.request.retarget input (target row 2)).x9Targets 0).val
        else ((sample row).z.targets gate bit).val) ∧
    final (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 0 + 1270 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 ((sample row).z.quotients gate bit).val ∧
    final (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 0 + 2540 + 254 * gate.val + bit.val)) =
      (((sample row).z.tables gate).get bit).trueRow := by
  have gateBound := gate.isLt
  have bitBound := bit.isLt
  have original := row_z_words (sample row) ram pointer (1017 + 9158 * row.val) stored
  have targetWord := gateData_target 5 5 _ ram pointer _ gate bit original
  have quotientWord := gateData_quotient 5 5 _ ram pointer _ gate bit original
  have tableWord := gateData_table 5 5 _ ram pointer _ gate bit original
  simp only [coordinateBitCount, Nat.reduceMul, Nat.add_assoc, Nat.add_zero, Nat.zero_add] at targetWord quotientWord tableWord
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · by_cases selected : gate = 4 ∧ bit = 0
    · rcases selected with ⟨rfl, rfl⟩
      simpa only [show (4 : Fin 5).val = 4 from rfl, show (0 : Fin 254).val = 0 from rfl, ↓reduceIte, Nat.mul_zero, Nat.add_zero, Fin.val_zero, Fin.val_ofNat, Nat.reduceMod,
        Nat.reduceMul, Nat.reduceAdd, Nat.add_assoc, and_self] using
        (pointRetargetFold_values sample input target pointer ram row).2.2
    · rw [if_neg selected]
      have different : ¬(gate.val = 4 ∧ bit.val = 0) := by
        rintro ⟨first, second⟩
        exact selected ⟨Fin.ext first, Fin.ext second⟩
      have unchanged := pointRetargetFold_free sample input target pointer ram row (0 + 254 * gate.val + bit.val)
        (by omega) (by omega) (by omega) (by omega)
      simp only [Nat.add_assoc, Nat.add_zero, Nat.zero_add] at unchanged
      simpa only [coordinateBitCount, Nat.add_assoc, Nat.add_zero, Nat.zero_add] using unchanged.trans targetWord
  · have unchanged := pointRetargetFold_free sample input target pointer ram row (0 + 1270 + 254 * gate.val + bit.val)
      (by omega) (by omega) (by omega) (by omega)
    simp only [Nat.add_assoc, Nat.add_zero, Nat.zero_add] at unchanged
    simpa only [coordinateBitCount, Nat.reduceMul, Nat.add_assoc, Nat.add_zero, Nat.zero_add] using unchanged.trans quotientWord
  · have unchanged := pointRetargetFold_free sample input target pointer ram row (0 + 2540 + 254 * gate.val + bit.val)
      (by omega) (by omega) (by omega) (by omega)
    simp only [Nat.add_assoc, Nat.add_zero, Nat.zero_add] at unchanged
    simpa only [coordinateBitCount, Nat.reduceMul, Nat.add_assoc, Nat.add_zero, Nat.zero_add] using unchanged.trans tableWord

end Kriterion.ArgoMAC.ArithmeticSimulator
