import Proof.Privacy.Simulator.Arithmetic.EncLinkLazy
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineLabels
import Proof.Privacy.Simulator.Arithmetic.OnlineInputBlock
import Proof.Privacy.Simulator.Arithmetic.OutputTargetsCode
import Proof.Privacy.Simulator.Arithmetic.EncLinkBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] onlineMachineCode onlineCurveCode onlinePointCode

/-- The online machine contains its input block. -/
theorem onlineMachine_input (attempts : Nat) :
    ContainsOnlineInput (onlineMachine attempts) (fun label : Fin 98 => onlineBodyLabels 1 97 (by decide) 98 label.val) := by
  intro pc inside
  have bound : pc.val < 97 := inside
  change (onlineMachineCode attempts)[((fun label : Fin 98 => onlineBodyLabels 1 97 (by decide) 98 label.val) pc).val]'((fun label : Fin 98 => onlineBodyLabels 1 97 (by decide) 98 label.val) pc).isLt =
    relocate (fun label : Fin 98 => onlineBodyLabels 1 97 (by decide) 98 label.val) ((onlineInput).code[pc.val])
  simp only [onlineBodyLabels_active _ _ _ _ _ bound]
  rw [onlineMachineCode_get]
  unfold onlineInstruction
  have guard0 : ¬ (1 + pc.val < 1) := by omega
  have guard1 : (1 + pc.val < 98) := by omega
  rw [dif_neg guard0, dif_pos guard1]
  simp only [Nat.add_sub_cancel_left]
  try rw [onlineCurveCode_eq]
  try rw [onlinePointCode_eq]
  rfl

/-- The online machine contains its samples block. -/
theorem onlineMachine_samples (attempts : Nat) :
    ContainsOnlineSampling (onlineMachine attempts) attempts (fun label : Fin 8772 => onlineBodyLabels 13622 8771 (by decide) 22393 label.val) := by
  intro pc inside
  have bound : pc.val < 8771 := inside
  change (onlineMachineCode attempts)[((fun label : Fin 8772 => onlineBodyLabels 13622 8771 (by decide) 22393 label.val) pc).val]'((fun label : Fin 8772 => onlineBodyLabels 13622 8771 (by decide) 22393 label.val) pc).isLt =
    relocate (fun label : Fin 8772 => onlineBodyLabels 13622 8771 (by decide) 22393 label.val) ((onlineSampling attempts).code[pc.val])
  simp only [onlineBodyLabels_active _ _ _ _ _ bound]
  rw [onlineMachineCode_get]
  unfold onlineInstruction
  have guard0 : ¬ (13622 + pc.val < 1) := by omega
  have guard1 : ¬ (13622 + pc.val < 98) := by omega
  have guard2 : ¬ (13622 + pc.val < 101) := by omega
  have guard3 : ¬ (13622 + pc.val < 7213) := by omega
  have guard4 : ¬ (13622 + pc.val < 13618) := by omega
  have guard5 : ¬ (13622 + pc.val < 13621) := by omega
  have guard6 : ¬ (13622 + pc.val < 13622) := by omega
  have guard7 : (13622 + pc.val < 22393) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_pos guard7]
  simp only [Nat.add_sub_cancel_left]
  try rw [onlineCurveCode_eq]
  try rw [onlinePointCode_eq]
  rfl

/-- The online machine contains its targets block. -/
theorem onlineMachine_targets (attempts : Nat) :
    ContainsOutputTargets (onlineMachine attempts) (fun label : Fin 4289 => onlineBodyLabels 22397 4288 (by decide) 26685 label.val) := by
  intro pc inside
  have bound : pc.val < 4288 := inside
  change (onlineMachineCode attempts)[((fun label : Fin 4289 => onlineBodyLabels 22397 4288 (by decide) 26685 label.val) pc).val]'((fun label : Fin 4289 => onlineBodyLabels 22397 4288 (by decide) 26685 label.val) pc).isLt =
    relocate (fun label : Fin 4289 => onlineBodyLabels 22397 4288 (by decide) 26685 label.val) ((outputTargetsMachine).code[pc.val])
  simp only [onlineBodyLabels_active _ _ _ _ _ bound]
  rw [onlineMachineCode_get]
  unfold onlineInstruction
  have guard0 : ¬ (22397 + pc.val < 1) := by omega
  have guard1 : ¬ (22397 + pc.val < 98) := by omega
  have guard2 : ¬ (22397 + pc.val < 101) := by omega
  have guard3 : ¬ (22397 + pc.val < 7213) := by omega
  have guard4 : ¬ (22397 + pc.val < 13618) := by omega
  have guard5 : ¬ (22397 + pc.val < 13621) := by omega
  have guard6 : ¬ (22397 + pc.val < 13622) := by omega
  have guard7 : ¬ (22397 + pc.val < 22393) := by omega
  have guard8 : ¬ (22397 + pc.val < 22397) := by omega
  have guard9 : (22397 + pc.val < 26685) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_pos guard9]
  simp only [Nat.add_sub_cancel_left]
  try rw [onlineCurveCode_eq]
  try rw [onlinePointCode_eq]
  rfl

/-- The online machine contains its link block. -/
theorem onlineMachine_link (attempts : Nat) :
    ContainsEncLink (onlineMachine attempts) attempts (fun label : Fin 7468 => onlineBranchLabels 1428193 7466 (by decide) 1435659 label.val) := by
  intro pc inside
  have bound : pc.val < 7466 := inside
  change (onlineMachineCode attempts)[((fun label : Fin 7468 => onlineBranchLabels 1428193 7466 (by decide) 1435659 label.val) pc).val]'((fun label : Fin 7468 => onlineBranchLabels 1428193 7466 (by decide) 1435659 label.val) pc).isLt =
    relocate (fun label : Fin 7468 => onlineBranchLabels 1428193 7466 (by decide) 1435659 label.val) ((encLink attempts).code[pc.val])
  simp only [onlineBranchLabels_active _ _ _ _ _ bound]
  rw [onlineMachineCode_get]
  unfold onlineInstruction
  have guard0 : ¬ (1428193 + pc.val < 1) := by omega
  have guard1 : ¬ (1428193 + pc.val < 98) := by omega
  have guard2 : ¬ (1428193 + pc.val < 101) := by omega
  have guard3 : ¬ (1428193 + pc.val < 7213) := by omega
  have guard4 : ¬ (1428193 + pc.val < 13618) := by omega
  have guard5 : ¬ (1428193 + pc.val < 13621) := by omega
  have guard6 : ¬ (1428193 + pc.val < 13622) := by omega
  have guard7 : ¬ (1428193 + pc.val < 22393) := by omega
  have guard8 : ¬ (1428193 + pc.val < 22397) := by omega
  have guard9 : ¬ (1428193 + pc.val < 26685) := by omega
  have guard10 : ¬ (1428193 + pc.val < 26688) := by omega
  have guard11 : ¬ (1428193 + pc.val < 1428185) := by omega
  have guard12 : ¬ (1428193 + pc.val < 1428193) := by omega
  have guard13 : (1428193 + pc.val < 1435659) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_neg guard11, dif_neg guard12, dif_pos guard13]
  simp only [Nat.add_sub_cancel_left]
  try rw [onlineCurveCode_eq]
  try rw [onlinePointCode_eq]
  rfl

/-- The online machine contains its curveGates block. -/
theorem onlineMachine_curveGates (attempts : Nat) :
    ContainsGateLoop (onlineMachine attempts) curveGatePlan attempts (by decide) (fun label : Fin 1315722 => onlineBranchLabels 1435662 1315720 (by decide) 2751382 label.val) := by
  intro pc inside
  have bound : pc.val < 1315720 := inside
  change (onlineMachineCode attempts)[((fun label : Fin 1315722 => onlineBranchLabels 1435662 1315720 (by decide) 2751382 label.val) pc).val]'((fun label : Fin 1315722 => onlineBranchLabels 1435662 1315720 (by decide) 2751382 label.val) pc).isLt =
    relocate (fun label : Fin 1315722 => onlineBranchLabels 1435662 1315720 (by decide) 2751382 label.val) ((gateLoop curveGatePlan attempts (by decide)).code[pc.val])
  simp only [onlineBranchLabels_active _ _ _ _ _ bound]
  rw [onlineMachineCode_get]
  unfold onlineInstruction
  have guard0 : ¬ (1435662 + pc.val < 1) := by omega
  have guard1 : ¬ (1435662 + pc.val < 98) := by omega
  have guard2 : ¬ (1435662 + pc.val < 101) := by omega
  have guard3 : ¬ (1435662 + pc.val < 7213) := by omega
  have guard4 : ¬ (1435662 + pc.val < 13618) := by omega
  have guard5 : ¬ (1435662 + pc.val < 13621) := by omega
  have guard6 : ¬ (1435662 + pc.val < 13622) := by omega
  have guard7 : ¬ (1435662 + pc.val < 22393) := by omega
  have guard8 : ¬ (1435662 + pc.val < 22397) := by omega
  have guard9 : ¬ (1435662 + pc.val < 26685) := by omega
  have guard10 : ¬ (1435662 + pc.val < 26688) := by omega
  have guard11 : ¬ (1435662 + pc.val < 1428185) := by omega
  have guard12 : ¬ (1435662 + pc.val < 1428193) := by omega
  have guard13 : ¬ (1435662 + pc.val < 1435659) := by omega
  have guard14 : ¬ (1435662 + pc.val < 1435662) := by omega
  have guard15 : (1435662 + pc.val < 2751382) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_neg guard11, dif_neg guard12, dif_neg guard13, dif_neg guard14, dif_pos guard15]
  simp only [Nat.add_sub_cancel_left]
  try rw [onlineCurveCode_eq]
  try rw [onlinePointCode_eq]
  rfl

/-- The online machine contains its pointGates block. -/
theorem onlineMachine_pointGates (attempts : Nat) :
    ContainsGateLoop (onlineMachine attempts) pointGatePlan attempts (by decide) (fun label : Fin 287353250 => onlineBranchLabels 2751388 287353248 (by decide) 290104636 label.val) := by
  intro pc inside
  have bound : pc.val < 287353248 := inside
  change (onlineMachineCode attempts)[((fun label : Fin 287353250 => onlineBranchLabels 2751388 287353248 (by decide) 290104636 label.val) pc).val]'((fun label : Fin 287353250 => onlineBranchLabels 2751388 287353248 (by decide) 290104636 label.val) pc).isLt =
    relocate (fun label : Fin 287353250 => onlineBranchLabels 2751388 287353248 (by decide) 290104636 label.val) ((gateLoop pointGatePlan attempts (by decide)).code[pc.val])
  simp only [onlineBranchLabels_active _ _ _ _ _ bound]
  rw [onlineMachineCode_get]
  unfold onlineInstruction
  have guard0 : ¬ (2751388 + pc.val < 1) := by omega
  have guard1 : ¬ (2751388 + pc.val < 98) := by omega
  have guard2 : ¬ (2751388 + pc.val < 101) := by omega
  have guard3 : ¬ (2751388 + pc.val < 7213) := by omega
  have guard4 : ¬ (2751388 + pc.val < 13618) := by omega
  have guard5 : ¬ (2751388 + pc.val < 13621) := by omega
  have guard6 : ¬ (2751388 + pc.val < 13622) := by omega
  have guard7 : ¬ (2751388 + pc.val < 22393) := by omega
  have guard8 : ¬ (2751388 + pc.val < 22397) := by omega
  have guard9 : ¬ (2751388 + pc.val < 26685) := by omega
  have guard10 : ¬ (2751388 + pc.val < 26688) := by omega
  have guard11 : ¬ (2751388 + pc.val < 1428185) := by omega
  have guard12 : ¬ (2751388 + pc.val < 1428193) := by omega
  have guard13 : ¬ (2751388 + pc.val < 1435659) := by omega
  have guard14 : ¬ (2751388 + pc.val < 1435662) := by omega
  have guard15 : ¬ (2751388 + pc.val < 2751382) := by omega
  have guard16 : ¬ (2751388 + pc.val < 2751385) := by omega
  have guard17 : ¬ (2751388 + pc.val < 2751388) := by omega
  have guard18 : (2751388 + pc.val < 290104636) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_neg guard11, dif_neg guard12, dif_neg guard13, dif_neg guard14, dif_neg guard15, dif_neg guard16, dif_neg guard17, dif_pos guard18]
  simp only [Nat.add_sub_cancel_left]
  try rw [onlineCurveCode_eq]
  try rw [onlinePointCode_eq]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The fixed-oracle simulator retains its private input block. -/
theorem lazyOnlineMachine_input :
    ContainsOnlineInput lazyOnlineMachine.arithmetic
      (fun label : Fin 98 => onlineBodyLabels 1 97 (by decide) 98 label.val) := by
  intro pc inside
  have bound : pc.val < 97 := inside
  rw [lazyOnlineMachine_private _ (by
    simp only [onlineBodyLabels_active _ _ _ _ _ bound]
    exact ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩)]
  exact onlineMachine_input 256 pc inside

/-- The fixed-oracle simulator retains its private samples block. -/
theorem lazyOnlineMachine_samples :
    ContainsOnlineSampling lazyOnlineMachine.arithmetic 256
      (fun label : Fin 8772 => onlineBodyLabels 13622 8771 (by decide) 22393 label.val) := by
  intro pc inside
  have bound : pc.val < 8771 := inside
  rw [lazyOnlineMachine_private _ (by
    simp only [onlineBodyLabels_active _ _ _ _ _ bound]
    exact ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩)]
  exact onlineMachine_samples 256 pc inside

/-- The fixed-oracle simulator retains its private targets block. -/
theorem lazyOnlineMachine_targets :
    ContainsOutputTargets lazyOnlineMachine.arithmetic
      (fun label : Fin 4289 => onlineBodyLabels 22397 4288 (by decide) 26685 label.val) := by
  intro pc inside
  have bound : pc.val < 4288 := inside
  rw [lazyOnlineMachine_private _ (by
    simp only [onlineBodyLabels_active _ _ _ _ _ bound]
    exact ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩)]
  exact onlineMachine_targets 256 pc inside

/-- The online machine uses the fixed-oracle link instructions. -/
theorem lazyOnlineMachine_link :
    ContainsLazyEncLink lazyOnlineMachine
      (fun label : Fin 7468 => onlineBranchLabels 1428193 7466 (by decide) 1435659 label.val) := by
  intro pc inside
  rw [lazyOnlineMachine_code]
  unfold lazyOnlineInstruction
  simp only [onlineBranchLabels_active _ _ _ _ _ inside, Fin.val_mk]
  rw [dif_pos (show 1428193 ≤ 1428193 + pc.val ∧ 1428193 + pc.val < 1435659 by omega)]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine uses the fixed-oracle curveGates instructions. -/
theorem lazyOnlineMachine_curveGates :
    ContainsLazyGateLoop lazyOnlineMachine curveGatePlan
      (fun label : Fin 1315722 => onlineBranchLabels 1435662 1315720 (by decide) 2751382 label.val) := by
  intro pc inside
  have bound : pc.val < 1315720 := inside
  rw [lazyOnlineMachine_code]
  unfold lazyOnlineInstruction
  simp only [onlineBranchLabels_active _ _ _ _ _ bound]
  rw [dif_neg (show ¬ (1428193 ≤ 1435662 + pc.val ∧ 1435662 + pc.val < 1435659) by omega)]
  rw [dif_pos (show 1435662 ≤ 1435662 + pc.val ∧ 1435662 + pc.val < 2751382 by omega)]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine uses the fixed-oracle pointGates instructions. -/
theorem lazyOnlineMachine_pointGates :
    ContainsLazyGateLoop lazyOnlineMachine pointGatePlan
      (fun label : Fin 287353250 => onlineBranchLabels 2751388 287353248 (by decide) 290104636 label.val) := by
  intro pc inside
  have bound : pc.val < 287353248 := inside
  rw [lazyOnlineMachine_code]
  unfold lazyOnlineInstruction
  simp only [onlineBranchLabels_active _ _ _ _ _ bound]
  rw [dif_neg (show ¬ (1428193 ≤ 2751388 + pc.val ∧ 2751388 + pc.val < 1435659) by omega)]
  rw [dif_neg (show ¬ (1435662 ≤ 2751388 + pc.val ∧ 2751388 + pc.val < 2751382) by omega)]
  rw [dif_pos (show 2751388 ≤ 2751388 + pc.val ∧ 2751388 + pc.val < 290104636 by omega)]
  simp only [Nat.add_sub_cancel_left]

end Kriterion.ArgoMAC.ArithmeticSimulator
