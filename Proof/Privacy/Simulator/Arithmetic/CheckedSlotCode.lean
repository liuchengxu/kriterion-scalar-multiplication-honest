import Construction.Simulator.CheckedSlot
import Proof.Privacy.Simulator.Arithmetic.LinearProgram
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

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

set_option backward.isDefEq.respectTransparency false in
/-- The fixed oracle capsule charges three instructions and rejects stale pairs. -/
theorem simulator_program_slot [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] (host : Simulator)
    (labels : Nat → Fin (host.size + 1))
    (constant : host.code[(labels 0).val] = .compute (.constant 0 14 (labels 1)))
    (loaded : host.code[(labels 1).val] = .compute (.load 1 0 (labels 2)))
    (program : host.code[(labels 2).val] = .program 0 9 8 1 2 (labels 3))
    (memory : Memory) (oracle : LazyOracle.State FixedIndex EncIndex) (fuel : Nat) :
    host.run (3 + fuel) ⟨labels 0, memory⟩ oracle =
      match queryFromRegisters 0 (memory.registers 9) (memory.registers 8) with
      | none => PMF.pure none
      | some query => match LazyOracle.program query
          (answerFromWords query (memory.ram (14#256)) (memory.registers 2)) oracle with
        | none => PMF.pure none
        | some updated =>
          (host.run fuel ⟨labels 3, { memory with registers := Function.update (Function.update memory.registers 0 14) 1 (memory.ram (14#256)) }⟩ updated).map
              (Option.map fun result => (result.1, result.2.1, result.2.2 + 3)) := by
  have prelude := simulator_linear_continue host [.constant 0 14, .load 1 0] labels
    (by
      intro index valid
      change index < 2 at valid
      interval_cases index
      · exact constant
      · exact loaded) memory oracle (fuel + 1)
  change host.run (2 + (fuel + 1)) ⟨labels 0, memory⟩ oracle = _ at prelude
  rw [show 3 + fuel = 2 + (fuel + 1) by omega, prelude]
  simp only [executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    List.length_cons, List.length_nil, Nat.reduceAdd]
  rw [Simulator.run]
  simp only [Simulator.step, program]
  simp only [Function.update_self]
  simp only [Function.update_of_ne (by decide : (9 : Register) ≠ 1),
    Function.update_of_ne (by decide : (9 : Register) ≠ 0),
    Function.update_of_ne (by decide : (8 : Register) ≠ 1),
    Function.update_of_ne (by decide : (8 : Register) ≠ 0),
    Function.update_of_ne (by decide : (2 : Register) ≠ 1),
    Function.update_of_ne (by decide : (2 : Register) ≠ 0)]
  cases decoded : queryFromRegisters (FixedIndex := FixedIndex) (EncIndex := EncIndex)
    0 (memory.registers 9) (memory.registers 8) with
  | none => simp [decoded, PMF.pure_map, PMF.pure_bind]
  | some query =>
      cases installed : LazyOracle.program query
        (answerFromWords query (memory.ram (14#256)) (memory.registers 2)) oracle <;>
        simp [decoded, installed, PMF.pure_map, PMF.pure_bind, PMF.map_comp,
          Option.map_map, Function.comp_def, Nat.add_assoc]

end Kriterion.ArgoMAC.ArithmeticSimulator
