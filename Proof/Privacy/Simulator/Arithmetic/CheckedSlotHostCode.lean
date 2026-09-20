import Proof.Privacy.Simulator.Arithmetic.CheckedSlotCode

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host keeps separate normal and cutoff returns. -/
def ContainsCheckedSlot (host : Machine) (attempts : Nat)
    (labels : Fin 305 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 305, pc ≠ 300 → pc ≠ 304 → host.code[(labels pc).val] =
    relocate labels ((checkedSlot attempts).code[pc.val]'pc.isLt)

/-- A contained fixed block retains its exact caller labels. -/
theorem checkedSlotBlock_linear (host : Machine) (attempts : Nat)
    (labels : Fin 305 → Fin (host.size + 1)) (present : ContainsCheckedSlot host attempts labels)
    (program : List LinearInstruction) (sourceLabels : Nat → Fin 305)
    (source : ContainsLinear (checkedSlot attempts) program sourceLabels)
    (inside : ∀ index, index < program.length → sourceLabels index ≠ 300 ∧ sourceLabels index ≠ 304) :
    ContainsLinear host program (labels ∘ sourceLabels) := by
  intro index valid
  exact (present (sourceLabels index) (inside index valid).1 (inside index valid).2).trans
    ((congrArg (relocate labels) (source index valid)).trans (LinearInstruction.relocate_emit labels _ _))

theorem checkedSlotBlock_start (host : Machine) (attempts : Nat)
    (labels : Fin 305 → Fin (host.size + 1)) (present : ContainsCheckedSlot host attempts labels) :
    ContainsLinear host checkedSlotStart (labels ∘ checkedSlotStartLabels) := by
  apply checkedSlotBlock_linear host attempts labels present checkedSlotStart checkedSlotStartLabels (checkedSlot_start attempts)
  intro index valid
  have bound : index < 12 := valid
  have value : (checkedSlotStartLabels index).val = 0 + index := by
    simp only [checkedSlotStartLabels, checkedSlotLinearLabels, dif_pos bound]
  constructor <;> intro equal <;> have vals := congrArg Fin.val equal <;> rw [value] at vals <;> change 0 + index = _ at vals <;> omega

theorem checkedSlotBlock_restore (host : Machine) (attempts : Nat)
    (labels : Fin 305 → Fin (host.size + 1)) (present : ContainsCheckedSlot host attempts labels) :
    ContainsLinear host checkedSlotRestore (labels ∘ checkedSlotRestoreLabels) := by
  apply checkedSlotBlock_linear host attempts labels present checkedSlotRestore checkedSlotRestoreLabels (checkedSlot_restore attempts)
  intro index valid
  have bound : index < 5 := valid
  have value : (checkedSlotRestoreLabels index).val = 56 + index := by
    simp only [checkedSlotRestoreLabels, checkedSlotLinearLabels, dif_pos bound]
  constructor <;> intro equal <;> have vals := congrArg Fin.val equal <;> rw [value] at vals <;> change 56 + index = _ at vals <;> omega

theorem checkedSlotBlock_target (host : Machine) (attempts : Nat)
    (labels : Fin 305 → Fin (host.size + 1)) (present : ContainsCheckedSlot host attempts labels) :
    ContainsLinear host checkedSlotTarget (labels ∘ checkedSlotTargetLabels) := by
  apply checkedSlotBlock_linear host attempts labels present checkedSlotTarget checkedSlotTargetLabels (checkedSlot_target attempts)
  intro index valid
  have bound : index < 4 := valid
  have value : (checkedSlotTargetLabels index).val = 260 + index := by
    simp only [checkedSlotTargetLabels, checkedSlotLinearLabels, dif_pos bound]
  constructor <;> intro equal <;> have vals := congrArg Fin.val equal <;> rw [value] at vals <;> change 260 + index = _ at vals <;> omega

theorem checkedSlotBlock_overlay (host : Machine) (attempts : Nat)
    (labels : Fin 305 → Fin (host.size + 1)) (present : ContainsCheckedSlot host attempts labels) :
    ContainsLinear host overlayAppend (labels ∘ checkedSlotOverlayLabels) := by
  apply checkedSlotBlock_linear host attempts labels present overlayAppend checkedSlotOverlayLabels (checkedSlot_overlay attempts)
  intro index valid
  have bound : index < 17 := valid
  have value : (checkedSlotOverlayLabels index).val = 264 + index := by
    simp only [checkedSlotOverlayLabels, checkedSlotLinearLabels, dif_pos bound]
  constructor <;> intro equal <;> have vals := congrArg Fin.val equal <;> rw [value] at vals <;> change 264 + index = _ at vals <;> omega

theorem checkedSlotBlock_history (host : Machine) (attempts : Nat)
    (labels : Fin 305 → Fin (host.size + 1)) (present : ContainsCheckedSlot host attempts labels) :
    ContainsLinear host checkedSlotHistory (labels ∘ checkedSlotHistoryLabels) := by
  apply checkedSlotBlock_linear host attempts labels present checkedSlotHistory checkedSlotHistoryLabels (checkedSlot_history attempts)
  intro index valid
  have bound : index < 4 := valid
  have value : (checkedSlotHistoryLabels index).val = 281 + index := by
    simp only [checkedSlotHistoryLabels, checkedSlotLinearLabels, dif_pos bound]
  constructor <;> intro equal <;> have vals := congrArg Fin.val equal <;> rw [value] at vals <;> change 281 + index = _ at vals <;> omega

theorem checkedSlotBlock_append (host : Machine) (attempts : Nat)
    (labels : Fin 305 → Fin (host.size + 1)) (present : ContainsCheckedSlot host attempts labels) :
    ContainsLinear host historyAppend (labels ∘ checkedSlotAppendLabels) := by
  apply checkedSlotBlock_linear host attempts labels present historyAppend checkedSlotAppendLabels (checkedSlot_append attempts)
  intro index valid
  have bound : index < 15 := valid
  have value : (checkedSlotAppendLabels index).val = 285 + index := by
    simp only [checkedSlotAppendLabels, checkedSlotLinearLabels, dif_pos bound]
  constructor <;> intro equal <;> have vals := congrArg Fin.val equal <;> rw [value] at vals <;> change 285 + index = _ at vals <;> omega

theorem checkedSlotBlock_collision (host : Machine) (attempts : Nat)
    (labels : Fin 305 → Fin (host.size + 1)) (present : ContainsCheckedSlot host attempts labels) :
    ContainsLinear host checkedSlotCollision (labels ∘ checkedSlotCollisionLabels) := by
  apply checkedSlotBlock_linear host attempts labels present checkedSlotCollision checkedSlotCollisionLabels (checkedSlot_collision attempts)
  intro index valid
  have bound : index < 3 := valid
  have value : (checkedSlotCollisionLabels index).val = 301 + index := by
    simp only [checkedSlotCollisionLabels, checkedSlotLinearLabels, dif_pos bound]
  constructor <;> intro equal <;> have vals := congrArg Fin.val equal <;> rw [value] at vals <;> change 301 + index = _ at vals <;> omega

theorem checkedSlotBlock_fresh (host : Machine) (attempts : Nat)
    (labels : Fin 305 → Fin (host.size + 1)) (present : ContainsCheckedSlot host attempts labels) :
    ContainsHistoryFresh host (labels ∘ checkedSlotFreshLabels) := by
  intro pc active
  have value : (checkedSlotFreshLabels pc).val = 12 + pc.val := by simp [checkedSlotFreshLabels, active]
  have first : checkedSlotFreshLabels pc ≠ 300 := by
    intro equal; have vals := congrArg Fin.val equal; rw [value] at vals; have bound := pc.isLt; omega
  have second : checkedSlotFreshLabels pc ≠ 304 := by
    intro equal; have vals := congrArg Fin.val equal; rw [value] at vals; have bound := pc.isLt; omega
  exact (present _ first second).trans ((congrArg (relocate labels) (checkedSlot_fresh attempts pc active)).trans
    (relocate_comp checkedSlotFreshLabels labels _))

theorem checkedSlotBlock_forward (host : Machine) (attempts : Nat)
    (labels : Fin 305 → Fin (host.size + 1)) (present : ContainsCheckedSlot host attempts labels) :
    ContainsInternalForward host attempts (labels ∘ checkedSlotForwardLabels) := by
  intro pc active
  have firstPc : pc ≠ 197 := by intro equal; have vals := congrArg Fin.val equal; omega
  have secondPc : pc ≠ 198 := by intro equal; have vals := congrArg Fin.val equal; omega
  have value : (checkedSlotForwardLabels pc).val = 61 + pc.val := by
    simp [checkedSlotForwardLabels, firstPc, secondPc]
  have first : checkedSlotForwardLabels pc ≠ 300 := by
    intro equal; have vals := congrArg Fin.val equal; rw [value] at vals; omega
  have second : checkedSlotForwardLabels pc ≠ 304 := by
    intro equal; have vals := congrArg Fin.val equal; rw [value] at vals; omega
  exact (present _ first second).trans ((congrArg (relocate labels) (checkedSlot_forward attempts pc active)).trans
    (relocate_comp checkedSlotForwardLabels labels _))

end Kriterion.ArgoMAC.ArithmeticSimulator
