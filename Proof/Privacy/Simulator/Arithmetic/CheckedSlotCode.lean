import Construction.Simulator.CheckedSlot
import Proof.Privacy.Simulator.Arithmetic.HistoryFreshBlock
import Proof.Privacy.Simulator.Arithmetic.InternalForwardBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The checked machine contains the complete start block. -/
theorem checkedSlot_start (attempts : Nat) : ContainsLinear (checkedSlot attempts) checkedSlotStart checkedSlotStartLabels := by
  intro index inside
  have bound : index < 12 := inside
  simp only [checkedSlotStartLabels, checkedSlotLinearLabels, dif_pos bound, checkedSlot, Vector.getElem_ofFn]
  rw [dif_pos (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.zero_add]
  try rfl

/-- The checked machine contains the complete restore block. -/
theorem checkedSlot_restore (attempts : Nat) : ContainsLinear (checkedSlot attempts) checkedSlotRestore checkedSlotRestoreLabels := by
  intro index inside
  have bound : index < 5 := inside
  simp only [checkedSlotRestoreLabels, checkedSlotLinearLabels, dif_pos bound, checkedSlot, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.zero_add]
  try rfl

/-- The checked machine contains the complete target block. -/
theorem checkedSlot_target (attempts : Nat) : ContainsLinear (checkedSlot attempts) checkedSlotTarget checkedSlotTargetLabels := by
  intro index inside
  have bound : index < 4 := inside
  simp only [checkedSlotTargetLabels, checkedSlotLinearLabels, dif_pos bound, checkedSlot, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.zero_add]
  try rfl

/-- The checked machine contains the complete overlay block. -/
theorem checkedSlot_overlay (attempts : Nat) : ContainsLinear (checkedSlot attempts) overlayAppend checkedSlotOverlayLabels := by
  intro index inside
  have bound : index < 17 := inside
  simp only [checkedSlotOverlayLabels, checkedSlotLinearLabels, dif_pos bound, checkedSlot, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.zero_add]
  try rfl

/-- The checked machine contains the complete history block. -/
theorem checkedSlot_history (attempts : Nat) : ContainsLinear (checkedSlot attempts) checkedSlotHistory checkedSlotHistoryLabels := by
  intro index inside
  have bound : index < 4 := inside
  simp only [checkedSlotHistoryLabels, checkedSlotLinearLabels, dif_pos bound, checkedSlot, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.zero_add]
  try rfl

/-- The checked machine contains the complete append block. -/
theorem checkedSlot_append (attempts : Nat) : ContainsLinear (checkedSlot attempts) historyAppend checkedSlotAppendLabels := by
  intro index inside
  have bound : index < 15 := inside
  simp only [checkedSlotAppendLabels, checkedSlotLinearLabels, dif_pos bound, checkedSlot, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.zero_add]
  try rfl

/-- The checked machine contains the complete collision block. -/
theorem checkedSlot_collision (attempts : Nat) : ContainsLinear (checkedSlot attempts) checkedSlotCollision checkedSlotCollisionLabels := by
  intro index inside
  have bound : index < 3 := inside
  simp only [checkedSlotCollisionLabels, checkedSlotLinearLabels, dif_pos bound, checkedSlot, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.zero_add]
  try rfl

/-- The checked machine contains the full freshness scan. -/
theorem checkedSlot_fresh (attempts : Nat) : ContainsHistoryFresh (checkedSlot attempts) checkedSlotFreshLabels := by
  intro pc active
  simp only [checkedSlotFreshLabels, if_neg active, checkedSlot, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_pos (by have bound := pc.isLt; omega)]
  simp only [Nat.add_sub_cancel_left, Nat.zero_add]
  try rfl

/-- The checked machine contains the complete internal forward call. -/
theorem checkedSlot_forward (attempts : Nat) :
    ContainsInternalForward (checkedSlot attempts) attempts checkedSlotForwardLabels := by
  intro pc active
  have first : pc ≠ 197 := by intro same; have vals := congrArg Fin.val same; omega
  have second : pc ≠ 198 := by intro same; have vals := congrArg Fin.val same; omega
  simp only [checkedSlotForwardLabels, if_neg first, if_neg second, checkedSlot, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega),
    dif_pos (by have bound := pc.isLt; omega)]
  simp only [Nat.add_sub_cancel_left, Nat.zero_add]
  try rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
