import Proof.Privacy.Simulator.Arithmetic.OnlineMachineLabels

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] onlineMachineCode onlineCurveCode onlinePointCode

/-- The online machine contains its inputSetup instruction block. -/
theorem onlineMachine_inputSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlineInputSetup
      (onlineBodyLabels 0 1 (by decide) 1) := by
  intro index inside
  have bound : index < 1 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 0 1 (by decide) 1 index).val ]'(onlineBodyLabels 0 1 (by decide) 1 index).isLt =
    (onlineInputSetup[index]'inside).emit (onlineBodyLabels 0 1 (by decide) 1 (index + 1))
  have next := onlineBodyLabels_next 0 1 (by decide) index bound
  change onlineBodyLabels 0 1 (by decide) 1 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 0 1 (by decide) 1 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : (0 + index < 1) := by omega
  rw [dif_pos guard0]
  simp only [Nat.zero_add]

/-- The online machine contains its originalSetup instruction block. -/
theorem onlineMachine_originalSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlineOriginalSetup
      (onlineBodyLabels 98 3 (by decide) 101) := by
  intro index inside
  have bound : index < 3 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 98 3 (by decide) 101 index).val ]'(onlineBodyLabels 98 3 (by decide) 101 index).isLt =
    (onlineOriginalSetup[index]'inside).emit (onlineBodyLabels 98 3 (by decide) 101 (index + 1))
  have next := onlineBodyLabels_next 98 3 (by decide) index bound
  change onlineBodyLabels 98 3 (by decide) 101 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 98 3 (by decide) 101 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (98 + index < 1) := by omega
  have guard1 : ¬ (98 + index < 98) := by omega
  have guard2 : (98 + index < 101) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_pos guard2]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its originalStore instruction block. -/
theorem onlineMachine_originalStore (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) selectedLabelStoreCode
      (onlineBodyLabels 101 7112 (by decide) 7213) := by
  intro index inside
  have bound : index < 7112 := by simpa only [selectedLabelStoreCode_length] using inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 101 7112 (by decide) 7213 index).val ]'(onlineBodyLabels 101 7112 (by decide) 7213 index).isLt =
    (selectedLabelStoreCode[index]'inside).emit (onlineBodyLabels 101 7112 (by decide) 7213 (index + 1))
  have next := onlineBodyLabels_next 101 7112 (by decide) index bound
  change onlineBodyLabels 101 7112 (by decide) 7213 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 101 7112 (by decide) 7213 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (101 + index < 1) := by omega
  have guard1 : ¬ (101 + index < 98) := by omega
  have guard2 : ¬ (101 + index < 101) := by omega
  have guard3 : (101 + index < 7213) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_pos guard3]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its curveRetarget instruction block. -/
theorem onlineMachine_curveRetarget (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) retargetCurveCode
      (onlineBodyLabels 7213 6405 (by decide) 13618) := by
  intro index inside
  have bound : index < 6405 := by simpa only [retargetCurveCode_length] using inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 7213 6405 (by decide) 13618 index).val ]'(onlineBodyLabels 7213 6405 (by decide) 13618 index).isLt =
    (retargetCurveCode[index]'inside).emit (onlineBodyLabels 7213 6405 (by decide) 13618 (index + 1))
  have next := onlineBodyLabels_next 7213 6405 (by decide) index bound
  change onlineBodyLabels 7213 6405 (by decide) 13618 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 7213 6405 (by decide) 13618 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (7213 + index < 1) := by omega
  have guard1 : ¬ (7213 + index < 98) := by omega
  have guard2 : ¬ (7213 + index < 101) := by omega
  have guard3 : ¬ (7213 + index < 7213) := by omega
  have guard4 : (7213 + index < 13618) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_pos guard4]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its sampleSetup instruction block. -/
theorem onlineMachine_sampleSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlineSampleSetup
      (onlineBodyLabels 13621 1 (by decide) 13622) := by
  intro index inside
  have bound : index < 1 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 13621 1 (by decide) 13622 index).val ]'(onlineBodyLabels 13621 1 (by decide) 13622 index).isLt =
    (onlineSampleSetup[index]'inside).emit (onlineBodyLabels 13621 1 (by decide) 13622 (index + 1))
  have next := onlineBodyLabels_next 13621 1 (by decide) index bound
  change onlineBodyLabels 13621 1 (by decide) 13622 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 13621 1 (by decide) 13622 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (13621 + index < 1) := by omega
  have guard1 : ¬ (13621 + index < 98) := by omega
  have guard2 : ¬ (13621 + index < 101) := by omega
  have guard3 : ¬ (13621 + index < 7213) := by omega
  have guard4 : ¬ (13621 + index < 13618) := by omega
  have guard5 : ¬ (13621 + index < 13621) := by omega
  have guard6 : (13621 + index < 13622) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_pos guard6]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its targetSetup instruction block. -/
theorem onlineMachine_targetSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlineTargetSetup
      (onlineBodyLabels 22393 4 (by decide) 22397) := by
  intro index inside
  have bound : index < 4 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 22393 4 (by decide) 22397 index).val ]'(onlineBodyLabels 22393 4 (by decide) 22397 index).isLt =
    (onlineTargetSetup[index]'inside).emit (onlineBodyLabels 22393 4 (by decide) 22397 (index + 1))
  have next := onlineBodyLabels_next 22393 4 (by decide) index bound
  change onlineBodyLabels 22393 4 (by decide) 22397 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 22393 4 (by decide) 22397 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (22393 + index < 1) := by omega
  have guard1 : ¬ (22393 + index < 98) := by omega
  have guard2 : ¬ (22393 + index < 101) := by omega
  have guard3 : ¬ (22393 + index < 7213) := by omega
  have guard4 : ¬ (22393 + index < 13618) := by omega
  have guard5 : ¬ (22393 + index < 13621) := by omega
  have guard6 : ¬ (22393 + index < 13622) := by omega
  have guard7 : ¬ (22393 + index < 22393) := by omega
  have guard8 : (22393 + index < 22397) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_pos guard8]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its retargetSetup instruction block. -/
theorem onlineMachine_retargetSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlineRetargetSetup
      (onlineBodyLabels 26685 3 (by decide) 26688) := by
  intro index inside
  have bound : index < 3 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 26685 3 (by decide) 26688 index).val ]'(onlineBodyLabels 26685 3 (by decide) 26688 index).isLt =
    (onlineRetargetSetup[index]'inside).emit (onlineBodyLabels 26685 3 (by decide) 26688 (index + 1))
  have next := onlineBodyLabels_next 26685 3 (by decide) index bound
  change onlineBodyLabels 26685 3 (by decide) 26688 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 26685 3 (by decide) 26688 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (26685 + index < 1) := by omega
  have guard1 : ¬ (26685 + index < 98) := by omega
  have guard2 : ¬ (26685 + index < 101) := by omega
  have guard3 : ¬ (26685 + index < 7213) := by omega
  have guard4 : ¬ (26685 + index < 13618) := by omega
  have guard5 : ¬ (26685 + index < 13621) := by omega
  have guard6 : ¬ (26685 + index < 13622) := by omega
  have guard7 : ¬ (26685 + index < 22393) := by omega
  have guard8 : ¬ (26685 + index < 22397) := by omega
  have guard9 : ¬ (26685 + index < 26685) := by omega
  have guard10 : (26685 + index < 26688) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_pos guard10]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its pointRetarget instruction block. -/
theorem onlineMachine_pointRetarget (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) retargetPointCode
      (onlineBodyLabels 26688 1401497 (by decide) 1428185) := by
  intro index inside
  have bound : index < 1401497 := by simpa only [retargetPointCode_length] using inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 26688 1401497 (by decide) 1428185 index).val ]'(onlineBodyLabels 26688 1401497 (by decide) 1428185 index).isLt =
    (retargetPointCode[index]'inside).emit (onlineBodyLabels 26688 1401497 (by decide) 1428185 (index + 1))
  have next := onlineBodyLabels_next 26688 1401497 (by decide) index bound
  change onlineBodyLabels 26688 1401497 (by decide) 1428185 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 26688 1401497 (by decide) 1428185 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (26688 + index < 1) := by omega
  have guard1 : ¬ (26688 + index < 98) := by omega
  have guard2 : ¬ (26688 + index < 101) := by omega
  have guard3 : ¬ (26688 + index < 7213) := by omega
  have guard4 : ¬ (26688 + index < 13618) := by omega
  have guard5 : ¬ (26688 + index < 13621) := by omega
  have guard6 : ¬ (26688 + index < 13622) := by omega
  have guard7 : ¬ (26688 + index < 22393) := by omega
  have guard8 : ¬ (26688 + index < 22397) := by omega
  have guard9 : ¬ (26688 + index < 26685) := by omega
  have guard10 : ¬ (26688 + index < 26688) := by omega
  have guard11 : (26688 + index < 1428185) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_pos guard11]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its linkSetup instruction block. -/
theorem onlineMachine_linkSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlineLinkSetup
      (onlineBodyLabels 1428185 8 (by decide) 1428193) := by
  intro index inside
  have bound : index < 8 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 1428185 8 (by decide) 1428193 index).val ]'(onlineBodyLabels 1428185 8 (by decide) 1428193 index).isLt =
    (onlineLinkSetup[index]'inside).emit (onlineBodyLabels 1428185 8 (by decide) 1428193 (index + 1))
  have next := onlineBodyLabels_next 1428185 8 (by decide) index bound
  change onlineBodyLabels 1428185 8 (by decide) 1428193 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 1428185 8 (by decide) 1428193 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (1428185 + index < 1) := by omega
  have guard1 : ¬ (1428185 + index < 98) := by omega
  have guard2 : ¬ (1428185 + index < 101) := by omega
  have guard3 : ¬ (1428185 + index < 7213) := by omega
  have guard4 : ¬ (1428185 + index < 13618) := by omega
  have guard5 : ¬ (1428185 + index < 13621) := by omega
  have guard6 : ¬ (1428185 + index < 13622) := by omega
  have guard7 : ¬ (1428185 + index < 22393) := by omega
  have guard8 : ¬ (1428185 + index < 22397) := by omega
  have guard9 : ¬ (1428185 + index < 26685) := by omega
  have guard10 : ¬ (1428185 + index < 26688) := by omega
  have guard11 : ¬ (1428185 + index < 1428185) := by omega
  have guard12 : (1428185 + index < 1428193) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_neg guard11, dif_pos guard12]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its curveSetup instruction block. -/
theorem onlineMachine_curveSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlineOriginalSetup
      (onlineBodyLabels 1435659 3 (by decide) 1435662) := by
  intro index inside
  have bound : index < 3 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 1435659 3 (by decide) 1435662 index).val ]'(onlineBodyLabels 1435659 3 (by decide) 1435662 index).isLt =
    (onlineOriginalSetup[index]'inside).emit (onlineBodyLabels 1435659 3 (by decide) 1435662 (index + 1))
  have next := onlineBodyLabels_next 1435659 3 (by decide) index bound
  change onlineBodyLabels 1435659 3 (by decide) 1435662 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 1435659 3 (by decide) 1435662 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (1435659 + index < 1) := by omega
  have guard1 : ¬ (1435659 + index < 98) := by omega
  have guard2 : ¬ (1435659 + index < 101) := by omega
  have guard3 : ¬ (1435659 + index < 7213) := by omega
  have guard4 : ¬ (1435659 + index < 13618) := by omega
  have guard5 : ¬ (1435659 + index < 13621) := by omega
  have guard6 : ¬ (1435659 + index < 13622) := by omega
  have guard7 : ¬ (1435659 + index < 22393) := by omega
  have guard8 : ¬ (1435659 + index < 22397) := by omega
  have guard9 : ¬ (1435659 + index < 26685) := by omega
  have guard10 : ¬ (1435659 + index < 26688) := by omega
  have guard11 : ¬ (1435659 + index < 1428185) := by omega
  have guard12 : ¬ (1435659 + index < 1428193) := by omega
  have guard13 : ¬ (1435659 + index < 1435659) := by omega
  have guard14 : (1435659 + index < 1435662) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_neg guard11, dif_neg guard12, dif_neg guard13, dif_pos guard14]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its pointSetup instruction block. -/
theorem onlineMachine_pointSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlinePointSetup
      (onlineBodyLabels 2751385 3 (by decide) 2751388) := by
  intro index inside
  have bound : index < 3 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 2751385 3 (by decide) 2751388 index).val ]'(onlineBodyLabels 2751385 3 (by decide) 2751388 index).isLt =
    (onlinePointSetup[index]'inside).emit (onlineBodyLabels 2751385 3 (by decide) 2751388 (index + 1))
  have next := onlineBodyLabels_next 2751385 3 (by decide) index bound
  change onlineBodyLabels 2751385 3 (by decide) 2751388 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 2751385 3 (by decide) 2751388 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (2751385 + index < 1) := by omega
  have guard1 : ¬ (2751385 + index < 98) := by omega
  have guard2 : ¬ (2751385 + index < 101) := by omega
  have guard3 : ¬ (2751385 + index < 7213) := by omega
  have guard4 : ¬ (2751385 + index < 13618) := by omega
  have guard5 : ¬ (2751385 + index < 13621) := by omega
  have guard6 : ¬ (2751385 + index < 13622) := by omega
  have guard7 : ¬ (2751385 + index < 22393) := by omega
  have guard8 : ¬ (2751385 + index < 22397) := by omega
  have guard9 : ¬ (2751385 + index < 26685) := by omega
  have guard10 : ¬ (2751385 + index < 26688) := by omega
  have guard11 : ¬ (2751385 + index < 1428185) := by omega
  have guard12 : ¬ (2751385 + index < 1428193) := by omega
  have guard13 : ¬ (2751385 + index < 1435659) := by omega
  have guard14 : ¬ (2751385 + index < 1435662) := by omega
  have guard15 : ¬ (2751385 + index < 2751382) := by omega
  have guard16 : ¬ (2751385 + index < 2751385) := by omega
  have guard17 : (2751385 + index < 2751388) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_neg guard11, dif_neg guard12, dif_neg guard13, dif_neg guard14, dif_neg guard15, dif_neg guard16, dif_pos guard17]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its labelSetup instruction block. -/
theorem onlineMachine_labelSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlineLabelSetup
      (onlineBodyLabels 290104636 2 (by decide) 290104638) := by
  intro index inside
  have bound : index < 2 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 290104636 2 (by decide) 290104638 index).val ]'(onlineBodyLabels 290104636 2 (by decide) 290104638 index).isLt =
    (onlineLabelSetup[index]'inside).emit (onlineBodyLabels 290104636 2 (by decide) 290104638 (index + 1))
  have next := onlineBodyLabels_next 290104636 2 (by decide) index bound
  change onlineBodyLabels 290104636 2 (by decide) 290104638 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 290104636 2 (by decide) 290104638 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (290104636 + index < 1) := by omega
  have guard1 : ¬ (290104636 + index < 98) := by omega
  have guard2 : ¬ (290104636 + index < 101) := by omega
  have guard3 : ¬ (290104636 + index < 7213) := by omega
  have guard4 : ¬ (290104636 + index < 13618) := by omega
  have guard5 : ¬ (290104636 + index < 13621) := by omega
  have guard6 : ¬ (290104636 + index < 13622) := by omega
  have guard7 : ¬ (290104636 + index < 22393) := by omega
  have guard8 : ¬ (290104636 + index < 22397) := by omega
  have guard9 : ¬ (290104636 + index < 26685) := by omega
  have guard10 : ¬ (290104636 + index < 26688) := by omega
  have guard11 : ¬ (290104636 + index < 1428185) := by omega
  have guard12 : ¬ (290104636 + index < 1428193) := by omega
  have guard13 : ¬ (290104636 + index < 1435659) := by omega
  have guard14 : ¬ (290104636 + index < 1435662) := by omega
  have guard15 : ¬ (290104636 + index < 2751382) := by omega
  have guard16 : ¬ (290104636 + index < 2751385) := by omega
  have guard17 : ¬ (290104636 + index < 2751388) := by omega
  have guard18 : ¬ (290104636 + index < 290104636) := by omega
  have guard19 : (290104636 + index < 290104638) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_neg guard11, dif_neg guard12, dif_neg guard13, dif_neg guard14, dif_neg guard15, dif_neg guard16, dif_neg guard17, dif_neg guard18, dif_pos guard19]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its labels instruction block. -/
theorem onlineMachine_labels (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) selectedLabelsCode
      (onlineBodyLabels 290104638 200660 (by decide) 290305298) := by
  intro index inside
  have bound : index < 200660 := by simpa only [selectedLabelsCode_length] using inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 290104638 200660 (by decide) 290305298 index).val ]'(onlineBodyLabels 290104638 200660 (by decide) 290305298 index).isLt =
    (selectedLabelsCode[index]'inside).emit (onlineBodyLabels 290104638 200660 (by decide) 290305298 (index + 1))
  have next := onlineBodyLabels_next 290104638 200660 (by decide) index bound
  change onlineBodyLabels 290104638 200660 (by decide) 290305298 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 290104638 200660 (by decide) 290305298 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (290104638 + index < 1) := by omega
  have guard1 : ¬ (290104638 + index < 98) := by omega
  have guard2 : ¬ (290104638 + index < 101) := by omega
  have guard3 : ¬ (290104638 + index < 7213) := by omega
  have guard4 : ¬ (290104638 + index < 13618) := by omega
  have guard5 : ¬ (290104638 + index < 13621) := by omega
  have guard6 : ¬ (290104638 + index < 13622) := by omega
  have guard7 : ¬ (290104638 + index < 22393) := by omega
  have guard8 : ¬ (290104638 + index < 22397) := by omega
  have guard9 : ¬ (290104638 + index < 26685) := by omega
  have guard10 : ¬ (290104638 + index < 26688) := by omega
  have guard11 : ¬ (290104638 + index < 1428185) := by omega
  have guard12 : ¬ (290104638 + index < 1428193) := by omega
  have guard13 : ¬ (290104638 + index < 1435659) := by omega
  have guard14 : ¬ (290104638 + index < 1435662) := by omega
  have guard15 : ¬ (290104638 + index < 2751382) := by omega
  have guard16 : ¬ (290104638 + index < 2751385) := by omega
  have guard17 : ¬ (290104638 + index < 2751388) := by omega
  have guard18 : ¬ (290104638 + index < 290104636) := by omega
  have guard19 : ¬ (290104638 + index < 290104638) := by omega
  have guard20 : (290104638 + index < 290305298) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_neg guard11, dif_neg guard12, dif_neg guard13, dif_neg guard14, dif_neg guard15, dif_neg guard16, dif_neg guard17, dif_neg guard18, dif_neg guard19, dif_pos guard20]
  simp only [Nat.add_sub_cancel_left]

end Kriterion.ArgoMAC.ArithmeticSimulator
