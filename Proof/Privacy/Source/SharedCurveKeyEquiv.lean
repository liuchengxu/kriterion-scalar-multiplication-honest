import Proof.Privacy.Source.SharedIndependentKeys
import Proof.Privacy.Collision.SharedCurvePadGuard

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography
noncomputable section
local instance curveKeyEquivFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveKeyEquivNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

private def curveLabelTripleEquiv :
    ((EncPRF.PermutationIndex → Block) × ((EncPRF.PermutationIndex → Block) × (EncPRF.PermutationIndex → Block))) ≃
    ((EncPRF.PermutationIndex → Block) × ((EncPRF.PermutationIndex → Block) × (EncPRF.PermutationIndex → Block))) where
  toFun sample := (sample.2.2, sample.2.1, fun index => sample.2.2 index ^^^ sample.1 index)
  invFun sample := (fun index => sample.1 index ^^^ sample.2.2 index, sample.2.1, sample.1)
  left_inv sample := by
    rcases sample with ⟨pads, selected, unused⟩
    apply Prod.ext
    · funext index
      exact (BitVec.xor_assoc _ _ _).symm.trans (by rw [BitVec.xor_self, BitVec.zero_xor])
    · rfl
  right_inv sample := by
    rcases sample with ⟨unused, selected, inactive⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext index
        exact (BitVec.xor_assoc _ _ _).symm.trans (by rw [BitVec.xor_self, BitVec.zero_xor])

/-- A uniform unused-pad array and two hidden label arrays give one independent point key. -/
def curveHiddenKeysEquiv (selected : EncPRF.PermutationIndex → Bool) :
    ((EncPRF.PermutationIndex → Block) × InputMacKey) ≃
      ((EncPRF.PermutationIndex → Block) × InputMacKey) :=
  (Equiv.prodCongr (Equiv.refl _) (selectedKeyLabelsEquiv (fun _ => true))).trans
    (curveLabelTripleEquiv.trans (Equiv.prodCongr (Equiv.refl _) (selectedKeyLabelsEquiv selected).symm))

/-- The key change of variables preserves the exact uniform source law. -/
theorem curveHiddenKeys_uniform [Fintype Block] (selected : EncPRF.PermutationIndex → Bool) :
    (PMF.uniformOfFintype ((EncPRF.PermutationIndex → Block) × InputMacKey)).map (curveHiddenKeysEquiv selected) =
      PMF.uniformOfFintype ((EncPRF.PermutationIndex → Block) × InputMacKey) :=
  map_uniformOfFintype_equivBetween (curveHiddenKeysEquiv selected)

/-- The changed variables are the retained unused curve labels and point key. -/
theorem curveHiddenKeys_source (context : Context) (pads : EncPRF.PermutationIndex → Block) (key : InputMacKey) :
    curveHiddenKeysEquiv (inputSelectedLabelBit context.input) (pads, key) =
      (curveUnused key, (({context with hiddenPointPads := pads}).curveHidden key).pointKey (curveUnused key)) := rfl

/-- The two reconstructed keys satisfy the exact EncPRF pad guard. -/
theorem curveHidden_pad_good_iff (context : Context) (key : InputMacKey) :
    EncSourceGood (context.curveKey (curveUnused key))
      ((context.curveHidden key).pointKey (curveUnused key)) ↔ ¬ curveHiddenPadBad context key := by
  rw [encSourceGood_iff]
  apply not_congr
  apply exists_congr
  intro index
  unfold linkingPad
  conv_lhs => lhs; rw [BitVec.xor_comm]
  conv_lhs => rhs; rw [BitVec.xor_comm]
  rw [curveKey_label, curveKey_label, pointKey_label, pointKey_label]
  change ((if false = inputSelectedLabelBit context.input index then context.activeCurveLabels index else curveUnused key index) ^^^
    (if false = inputSelectedLabelBit context.input index then inputKeyLabel key index true
      else curveUnused key index ^^^ context.hiddenPointPads index)) =
    ((if true = inputSelectedLabelBit context.input index then context.activeCurveLabels index else curveUnused key index) ^^^
    (if true = inputSelectedLabelBit context.input index then inputKeyLabel key index true
      else curveUnused key index ^^^ context.hiddenPointPads index)) ↔ _
  cases selected : inputSelectedLabelBit context.input index <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, if_true, if_false,
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · constructor
    · intro equal
      have shifted := congrArg (fun value => context.activeCurveLabels index ^^^ value) equal
      simpa only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using shifted
    · intro equal
      rw [equal, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · constructor
    · intro equal
      have shifted := congrArg (fun value => context.activeCurveLabels index ^^^ value) equal.symm
      simpa only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using shifted
    · intro equal
      rw [equal, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end
end Kriterion.ArgoMAC.Security.SharedRetained
