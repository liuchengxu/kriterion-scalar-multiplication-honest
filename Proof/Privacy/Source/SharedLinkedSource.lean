import Proof.Privacy.Source.SharedRawAssembly

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 2048

/-- This key contains the visible selected labels and the retained unused labels. -/
def Context.curveKey (context : Context) (labels : EncPRF.PermutationIndex → Block) : InputMacKey :=
  (selectedKeyLabelsEquiv (inputSelectedLabelBit context.input)).symm (context.activeCurveLabels, labels)

/-- The reconstructed key gives exactly its selected or unused label. -/
theorem curveKey_label (context : Context) (labels : EncPRF.PermutationIndex → Block)
    (index : EncPRF.PermutationIndex) (branch : Bool) :
    inputKeyLabel (context.curveKey labels) index branch =
      if branch = inputSelectedLabelBit context.input index then context.activeCurveLabels index else labels index := by
  unfold Context.curveKey
  change inputKeyLabel (inputKeyLabelEquiv.symm (fun wire bit =>
    if bit = inputSelectedLabelBit context.input wire then context.activeCurveLabels wire else labels wire)) index branch = _
  exact congrFun (congrFun (inputKeyLabelEquiv.apply_symm_apply
    (fun wire bit => if bit = inputSelectedLabelBit context.input wire
      then context.activeCurveLabels wire else labels wire)) index) branch

private theorem actualGate_label (pointKey curveKey : InputMacKey)
    (gate : RawCircuitGate) (branch : Bool) :
    BitAdaptor.encode (circuitGateKey pointKey curveKey gate) branch =
      match gate with
      | .inl _ => inputKeyLabel curveKey (circuitGateWire gate) branch
      | .inr _ => inputKeyLabel pointKey (circuitGateWire gate) branch := by
  rcases gate with ⟨family, position⟩ | ⟨row, family⟩
  · fin_cases family <;> rfl
  · rcases family with ⟨family, position⟩ | (⟨family, position⟩ | ⟨family, position⟩) <;>
      fin_cases family <;> rfl

/-- This condition retains the actual EncPRF shifts in both label branches. -/
def Context.Linked (context : Context) (oracle : SimulatorOracleCoin) (bridgeKey : BaseField) : Prop :=
  ∀ index,
    context.activePointLabels index = context.activeCurveLabels index ^^^
      evenMansour (oracle.encOracle.permutation index) (EncPRF.whiteningKeys oracle.hashOracle bridgeKey)
        (inputSelectedLabelBit context.input index) ∧
    context.hiddenPointPads index =
      evenMansour (oracle.encOracle.permutation index) (EncPRF.whiteningKeys oracle.hashOracle bridgeKey)
        (!(inputSelectedLabelBit context.input index))

/-- Linked retained labels equal the actual input and transformed point keys. -/
theorem linked_gateLabel (context : Context) (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (linked : context.Linked oracle bridgeKey) (labels : EncPRF.PermutationIndex → Block)
    (gate : RawCircuitGate) (branch : Bool) :
    context.gateLabel labels gate branch =
      BitAdaptor.encode (circuitGateKey (EncPRF.transformKey oracle.encOracle
        (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) (context.curveKey labels))
        (context.curveKey labels) gate) branch := by
  rw [actualGate_label]
  cases gate with
  | inl gate => exact (curveKey_label context labels _ branch).symm
  | inr gate =>
      rw [linkedLabel_fixedShift, curveKey_label]
      unfold Context.gateLabel
      dsimp only
      by_cases selected : branch = inputSelectedLabelBit context.input (circuitGateWire (.inr gate))
      · rw [if_pos selected, if_pos selected, selected, (linked _).1]
      · rw [if_neg selected, if_neg selected, (linked _).2]
        rw [Bool.eq_not_iff.mpr selected]

/-- The retained raw prescriptions equal the actual linked-key source prescriptions. -/
theorem linked_gates (context : Context) (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (linked : context.Linked oracle bridgeKey)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block)) :
    context.gates sample = sourceGatePrescription (context.source sample.1)
      (EncPRF.transformKey oracle.encOracle (EncPRF.whiteningKeys oracle.hashOracle bridgeKey)
        (context.curveKey sample.2)) (context.curveKey sample.2) (context.lifts sample.1) := by
  funext gate
  have falseLabel := linked_gateLabel context oracle bridgeKey linked sample.2 gate false
  have trueLabel := linked_gateLabel context oracle bridgeKey linked sample.2 gate true
  have key : (⟨context.gateLabel sample.2 gate false, context.gateLabel sample.2 gate true⟩ : BitAdaptor.Key) =
      circuitGateKey (EncPRF.transformKey oracle.encOracle (EncPRF.whiteningKeys oracle.hashOracle bridgeKey)
        (context.curveKey sample.2)) (context.curveKey sample.2) gate := by
    cases selectedKey : circuitGateKey (EncPRF.transformKey oracle.encOracle
        (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) (context.curveKey sample.2))
        (context.curveKey sample.2) gate
    simp only [selectedKey, BitAdaptor.encode] at falseLabel trueLabel
    rw [falseLabel, trueLabel]
    simp only [Bool.false_eq_true, if_false, if_true]
  simp only [Context.gates, sourceGatePrescription, circuitRawGatePrescription, key]

/-- The actual linked-key source inherits every shared bucket injection. -/
theorem linked_assignments_injective (context : Context) (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (linked : context.Linked oracle bridgeKey)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (good : ¬ context.collision sample) (index : Shared.FixedKeyIndex) :
    let gates := sourceGatePrescription (context.source sample.1)
      (EncPRF.transformKey oracle.encOracle (EncPRF.whiteningKeys oracle.hashOracle bridgeKey)
        (context.curveKey sample.2)) (context.curveKey sample.2) (context.lifts sample.1)
    Function.Injective (sharedRawBucketDomain gates index) ∧
      Function.Injective (sharedRawBucketRange gates index) := by
  rw [← linked_gates context oracle bridgeKey linked sample]
  exact raw_assignments_injective context sample good index

end
end Kriterion.ArgoMAC.Security.SharedRetained
