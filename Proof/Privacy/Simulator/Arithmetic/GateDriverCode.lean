import Construction.Simulator.GateDriver
import Proof.Privacy.Simulator.Arithmetic.CheckedSlotBlock
import Proof.Privacy.Simulator.Arithmetic.GateDirectiveSource
import Proof.Privacy.Simulator.Arithmetic.GateDirectiveScratch

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The gate machine contains its complete load block. -/
theorem gateDriver_load (attempts : Nat) (gate : GateCode) :
    ContainsLinear (gateDriver attempts gate) (gateDirectiveLoad gate.selected gate.target gate.quotient gate.table) gateDriverLoadLabels := by
  intro index inside
  have bound : index < 21 := inside
  simp only [gateDriverLoadLabels, gateDriverLinearLabels, dif_pos bound, gateDriver, Vector.getElem_ofFn]
  rw [dif_pos (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.zero_add]
  try rfl

/-- The gate machine contains its complete save block. -/
theorem gateDriver_save (attempts : Nat) (gate : GateCode) :
    ContainsLinear (gateDriver attempts gate) gateDirectiveSave gateDriverSaveLabels := by
  intro index inside
  have bound : index < 20 := inside
  simp only [gateDriverSaveLabels, gateDriverLinearLabels, dif_pos bound, gateDriver, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.zero_add]
  try rfl

/-- The gate machine contains its complete load0 block. -/
theorem gateDriver_load0 (attempts : Nat) (gate : GateCode) :
    ContainsLinear (gateDriver attempts gate) (gateSlotLoad (gate.oracle 0) 0) (gateDriverSlotLoadLabels 0) := by
  change ContainsLinear (gateDriver attempts gate) (gateSlotLoad (gate.oracle 0) 0)
    (gateDriverLinearLabels 80 8 (by decide) 88)
  intro index inside
  have bound : index < 8 := inside
  simp only [gateDriverLinearLabels, dif_pos bound, gateDriver, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.zero_add]
  try rfl

/-- The gate machine contains its complete load1 block. -/
theorem gateDriver_load1 (attempts : Nat) (gate : GateCode) :
    ContainsLinear (gateDriver attempts gate) (gateSlotLoad (gate.oracle 1) 1) (gateDriverSlotLoadLabels 1) := by
  change ContainsLinear (gateDriver attempts gate) (gateSlotLoad (gate.oracle 1) 1)
    (gateDriverLinearLabels 393 8 (by decide) 401)
  intro index inside
  have bound : index < 8 := inside
  simp only [gateDriverLinearLabels, dif_pos bound, gateDriver, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.zero_add]
  try rfl

/-- The gate machine contains its complete test block. -/
theorem gateDriver_test (attempts : Nat) (gate : GateCode) :
    ContainsLinear (gateDriver attempts gate) gateDriverTest gateDriverTestLabels := by
  intro index inside
  have bound : index < 4 := inside
  simp only [gateDriverTestLabels, gateDriverLinearLabels, dif_pos bound, gateDriver, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.zero_add]
  try rfl

/-- The gate machine contains its complete load2 block. -/
theorem gateDriver_load2 (attempts : Nat) (gate : GateCode) :
    ContainsLinear (gateDriver attempts gate) (gateSlotLoad (gate.oracle 2) 2) (gateDriverSlotLoadLabels 2) := by
  change ContainsLinear (gateDriver attempts gate) (gateSlotLoad (gate.oracle 2) 2)
    (gateDriverLinearLabels 711 8 (by decide) 719)
  intro index inside
  have bound : index < 8 := inside
  simp only [gateDriverLinearLabels, dif_pos bound, gateDriver, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.zero_add]
  try rfl

/-- The gate machine contains its complete restore block. -/
theorem gateDriver_restore (attempts : Nat) (gate : GateCode) :
    ContainsLinear (gateDriver attempts gate) gateDirectiveRestore gateDriverRestoreLabels := by
  intro index inside
  have bound : index < 10 := inside
  simp only [gateDriverRestoreLabels, gateDriverLinearLabels, dif_pos bound, gateDriver, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.zero_add]
  try rfl

/-- The gate machine contains its selected hash or pad arithmetic. -/
theorem gateDriver_blocks (attempts : Nat) (gate : GateCode) :
    ContainsGateBlocks (gateDriver attempts gate) gate.tweak gateDriverBlocksLabels := by
  intro pc active
  have notExit : pc ≠ 38 := by intro equal; have vals := congrArg Fin.val equal; omega
  simp only [gateDriverBlocksLabels, if_neg notExit, gateDriver, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_pos (by have bound := pc.isLt; omega)]
  simp only [Nat.add_sub_cancel_left]
  try rfl

/-- Slot 0 executes the full checked programming machine. -/
theorem gateDriver_slot0 (attempts : Nat) (gate : GateCode) :
    ContainsCheckedSlot (gateDriver attempts gate) attempts (gateDriverSlotLabels 0) := by
  intro pc normal cutoff
  simp only [gateDriverSlotLabels, show (0 : Fin 3).val = 0 from rfl, show (1 : Fin 3).val = 1 from rfl, show (2 : Fin 3).val = 2 from rfl, if_neg cutoff, if_neg normal, gateDriver, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by have bound := pc.isLt; omega)]
  simp only [Nat.add_sub_cancel_left]
  try rfl

/-- Slot 1 executes the full checked programming machine. -/
theorem gateDriver_slot1 (attempts : Nat) (gate : GateCode) :
    ContainsCheckedSlot (gateDriver attempts gate) attempts (gateDriverSlotLabels 1) := by
  intro pc normal cutoff
  simp only [gateDriverSlotLabels, show (0 : Fin 3).val = 0 from rfl, show (1 : Fin 3).val = 1 from rfl, show (2 : Fin 3).val = 2 from rfl, if_neg cutoff, if_neg normal, gateDriver, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by have bound := pc.isLt; omega)]
  simp only [Nat.add_sub_cancel_left]
  try rfl

/-- Slot 2 executes the full checked programming machine. -/
theorem gateDriver_slot2 (attempts : Nat) (gate : GateCode) :
    ContainsCheckedSlot (gateDriver attempts gate) attempts (gateDriverSlotLabels 2) := by
  intro pc normal cutoff
  simp only [gateDriverSlotLabels, show (0 : Fin 3).val = 0 from rfl, show (1 : Fin 3).val = 1 from rfl, show (2 : Fin 3).val = 2 from rfl, if_neg cutoff, if_neg normal, gateDriver, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by have bound := pc.isLt; omega)]
  simp only [Nat.add_sub_cancel_left]
  try rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
