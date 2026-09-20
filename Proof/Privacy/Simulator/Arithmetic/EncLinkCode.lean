import Proof.Privacy.Simulator.Arithmetic.EncLinkMachine
import Proof.Privacy.Simulator.Arithmetic.EncLinkArithmetic
import Proof.Privacy.Simulator.Arithmetic.EncLinkIndex
import Proof.Privacy.Simulator.Arithmetic.InternalForwardBlock
import Proof.Privacy.Simulator.Arithmetic.HashHandlerBlock
import Proof.Privacy.Simulator.Arithmetic.WordInputBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The complete link contains the save block. -/
theorem encLink_save (attempts : Nat) :
    ContainsLinear (encLink attempts) encLinkSave encLinkSaveLabels := by
  intro index valid
  have bound : index < 15 := valid
  simp [encLink,
    show ¬ (7464 ≤ index ∧ index < 7466) by omega,
    encLinkSaveLabels,
    encLinkLabels,
    bound]

/-- The complete link contains the hash block. -/
theorem encLink_hash (attempts : Nat) :
    ContainsHashHandler (encLink attempts) encLinkHashLabels := by
  intro pc valid
  have bound : pc.val < 73 := by
    have := pc.isLt
    have : pc.val ≠ 73 := by intro equal; exact valid (Fin.ext equal)
    omega
  simp [encLink,
    show ¬ (7464 ≤ 15 + pc.val ∧ 15 + pc.val < 7466) by omega,
    encLinkHashLabels,
    encLinkLabels,
    bound,
    show ¬ 15 + pc.val < 15 by omega,
    show 15 ≤ 15 + pc.val by omega,
    show 15 + pc.val < 88 by omega]
  rfl

/-- The complete link contains the whitening block. -/
theorem encLink_whitening (attempts : Nat) :
    ContainsLinear (encLink attempts) encLinkWhitening encLinkWhiteningLabels := by
  intro index valid
  have bound : index < 8 := valid
  simp [encLink,
    show ¬ (7464 ≤ 88 + index ∧ 88 + index < 7466) by omega,
    encLinkWhiteningLabels,
    encLinkLabels,
    bound,
    show ¬ 88 + index < 15 by omega,
    show ¬ (15 ≤ 88 + index ∧ 88 + index < 88) by omega,
    show 88 ≤ 88 + index by omega,
    show 88 + index < 96 by omega]

/-- The complete link contains the indices block. -/
theorem encLink_indices (attempts : Nat) :
    ContainsLinear (encLink attempts) encLinkIndexPrelude encLinkIndexLabels := by
  intro index valid
  have bound : index < 7112 := by simpa only [encLinkIndexPrelude_length] using valid
  simp [encLink,
    show ¬ (7464 ≤ 96 + index ∧ 96 + index < 7466) by omega,
    encLinkIndexLabels,
    encLinkLabels,
    bound,
    show ¬ 96 + index < 15 by omega,
    show ¬ (15 ≤ 96 + index ∧ 96 + index < 88) by omega,
    show ¬ (88 ≤ 96 + index ∧ 96 + index < 96) by omega,
    show 96 ≤ 96 + index by omega,
    show 96 + index < 7208 by omega]

/-- The complete link contains the reader block. -/
theorem encLink_reader (attempts : Nat) :
    ContainsWordInput (encLink attempts) 14 encLinkReaderLabels := by
  intro pc valid
  have bound : pc.val < 14 := valid
  simp [encLink,
    show ¬ (7464 ≤ 7208 + pc.val ∧ 7208 + pc.val < 7466) by omega,
    encLinkReaderLabels,
    encLinkLabels,
    bound,
    show ¬ 7208 + pc.val < 15 by omega,
    show ¬ (15 ≤ 7208 + pc.val ∧ 7208 + pc.val < 88) by omega,
    show ¬ (88 ≤ 7208 + pc.val ∧ 7208 + pc.val < 96) by omega,
    show ¬ (96 ≤ 7208 + pc.val ∧ 7208 + pc.val < 7208) by omega,
    show 7208 ≤ 7208 + pc.val by omega,
    show 7208 + pc.val < 7222 by omega]

/-- The complete link contains the prepare block. -/
theorem encLink_prepare (attempts : Nat) :
    ContainsLinear (encLink attempts) encLinkPrepare encLinkPrepareLabels := by
  intro index valid
  have bound : index < 17 := valid
  simp [encLink,
    show ¬ (7464 ≤ 7222 + index ∧ 7222 + index < 7466) by omega,
    encLinkPrepareLabels,
    encLinkLabels,
    bound,
    show ¬ 7222 + index < 15 by omega,
    show ¬ (15 ≤ 7222 + index ∧ 7222 + index < 88) by omega,
    show ¬ (88 ≤ 7222 + index ∧ 7222 + index < 96) by omega,
    show ¬ (96 ≤ 7222 + index ∧ 7222 + index < 7208) by omega,
    show ¬ (7208 ≤ 7222 + index ∧ 7222 + index < 7222) by omega,
    show 7222 ≤ 7222 + index by omega,
    show 7222 + index < 7239 by omega]

/-- The complete link contains the query block. -/
theorem encLink_query (attempts : Nat) :
    ContainsInternalForward (encLink attempts) attempts encLinkQueryLabels := by
  intro pc valid
  have bound : pc.val < 197 := valid
  simp [encLink,
    show ¬ (7464 ≤ 7239 + pc.val ∧ 7239 + pc.val < 7466) by omega,
    encLinkQueryLabels,
    bound,
    show ¬ 7239 + pc.val < 15 by omega,
    show ¬ (15 ≤ 7239 + pc.val ∧ 7239 + pc.val < 88) by omega,
    show ¬ (88 ≤ 7239 + pc.val ∧ 7239 + pc.val < 96) by omega,
    show ¬ (96 ≤ 7239 + pc.val ∧ 7239 + pc.val < 7208) by omega,
    show ¬ (7208 ≤ 7239 + pc.val ∧ 7239 + pc.val < 7222) by omega,
    show ¬ (7222 ≤ 7239 + pc.val ∧ 7239 + pc.val < 7239) by omega,
    show 7239 ≤ 7239 + pc.val by omega,
    show 7239 + pc.val < 7436 by omega]
  rfl

/-- The complete link contains the finish block. -/
theorem encLink_finish (attempts : Nat) :
    ContainsLinear (encLink attempts) encLinkFinish encLinkFinishLabels := by
  intro index valid
  have bound : index < 20 := valid
  simp [encLink,
    show ¬ (7464 ≤ 7436 + index ∧ 7436 + index < 7466) by omega,
    encLinkFinishLabels,
    encLinkLabels,
    bound,
    show ¬ 7436 + index < 15 by omega,
    show ¬ (15 ≤ 7436 + index ∧ 7436 + index < 88) by omega,
    show ¬ (88 ≤ 7436 + index ∧ 7436 + index < 96) by omega,
    show ¬ (96 ≤ 7436 + index ∧ 7436 + index < 7208) by omega,
    show ¬ (7208 ≤ 7436 + index ∧ 7436 + index < 7222) by omega,
    show ¬ (7222 ≤ 7436 + index ∧ 7436 + index < 7239) by omega,
    show ¬ (7239 ≤ 7436 + index ∧ 7436 + index < 7436) by omega,
    show 7436 ≤ 7436 + index by omega,
    show 7436 + index < 7456 by omega]

/-- The complete link contains the switch block. -/
theorem encLink_switch (attempts : Nat) :
    ContainsLinear (encLink attempts) encLinkSwitch encLinkSwitchLabels := by
  intro index valid
  have bound : index < 4 := valid
  simp [encLink,
    show ¬ (7464 ≤ 7460 + index ∧ 7460 + index < 7466) by omega,
    encLinkSwitchLabels,
    encLinkLabels,
    bound,
    show ¬ 7460 + index < 15 by omega,
    show ¬ (15 ≤ 7460 + index ∧ 7460 + index < 88) by omega,
    show ¬ (88 ≤ 7460 + index ∧ 7460 + index < 96) by omega,
    show ¬ (96 ≤ 7460 + index ∧ 7460 + index < 7208) by omega,
    show ¬ (7208 ≤ 7460 + index ∧ 7460 + index < 7222) by omega,
    show ¬ (7222 ≤ 7460 + index ∧ 7460 + index < 7239) by omega,
    show ¬ (7239 ≤ 7460 + index ∧ 7460 + index < 7436) by omega,
    show ¬ (7436 ≤ 7460 + index ∧ 7460 + index < 7456) by omega,
    show 7460 ≤ 7460 + index by omega,
    show 7460 + index < 7464 by omega]

/-- The complete link contains the result block. -/
theorem encLink_result (attempts : Nat) :
    ContainsLinear (encLink attempts) encLinkReturn encLinkReturnLabels := by
  intro index valid
  have bound : index < 2 := valid
  simp only [encLinkReturnLabels, encLinkLabels, bound, ↓reduceDIte]
  simp only [encLink, Vector.getElem_ofFn,
    show 7464 ≤ 7464 + index by omega, show 7464 + index < 7466 by omega,
    and_self, ↓reduceDIte, Nat.add_sub_cancel_left]
  rfl


/-- The loop controller has four fixed instructions. -/
theorem encLink_controlCode (attempts : Nat) :
    (encLink attempts).code[7456]'(by change 7456 < 7468; decide) = .branch 2 7464 7457 ∧
    (encLink attempts).code[7457]'(by change 7457 < 7468; decide) = .constant 3 254 7458 ∧
    (encLink attempts).code[7458]'(by change 7458 < 7468; decide) = .arithmetic .xor 3 2 3 7459 ∧
    (encLink attempts).code[7459]'(by change 7459 < 7468; decide) = .branch 3 7460 7208 := by
  simp [encLink]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
