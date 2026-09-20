import Proof.Privacy.Source.SharedCurveStable

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 2048

/-- This point key keeps the selected point labels and shifted unused labels. -/
def Context.pointKey (context : Context) (labels : EncPRF.PermutationIndex → Block) : InputMacKey :=
  ({context with activeCurveLabels := context.activePointLabels}).curveKey
    (fun index => labels index ^^^ context.hiddenPointPads index)

/-- The independent point key gives the exact retained label in each branch. -/
theorem pointKey_label (context : Context) (labels : EncPRF.PermutationIndex → Block)
    (index : EncPRF.PermutationIndex) (branch : Bool) :
    inputKeyLabel (context.pointKey labels) index branch =
      if branch = inputSelectedLabelBit context.input index then context.activePointLabels index
        else labels index ^^^ context.hiddenPointPads index :=
  curveKey_label _ _ index branch

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

/-- The two retained keys give every raw gate its exact branch label. -/
theorem independent_gateLabel (context : Context) (labels : EncPRF.PermutationIndex → Block)
    (gate : RawCircuitGate) (branch : Bool) :
    context.gateLabel labels gate branch =
      BitAdaptor.encode (circuitGateKey (context.pointKey labels) (context.curveKey labels) gate) branch := by
  rw [actualGate_label]
  cases gate with
  | inl gate => exact (curveKey_label context labels _ branch).symm
  | inr gate => exact (pointKey_label context labels _ branch).symm

/-- The retained source equals the raw source with its two independent keys. -/
theorem independent_gates (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block)) :
    context.gates sample = sourceGatePrescription (context.source sample.1)
      (context.pointKey sample.2) (context.curveKey sample.2) (context.lifts sample.1) := by
  funext gate
  have falseLabel := independent_gateLabel context sample.2 gate false
  have trueLabel := independent_gateLabel context sample.2 gate true
  have key : (⟨context.gateLabel sample.2 gate false, context.gateLabel sample.2 gate true⟩ : BitAdaptor.Key) =
      circuitGateKey (context.pointKey sample.2) (context.curveKey sample.2) gate := by
    cases selectedKey : circuitGateKey (context.pointKey sample.2) (context.curveKey sample.2) gate
    simp only [selectedKey, BitAdaptor.encode] at falseLabel trueLabel
    rw [falseLabel, trueLabel]
    simp only [Bool.false_eq_true, if_false, if_true]
  simp only [Context.gates, sourceGatePrescription, circuitRawGatePrescription, key]

end
end Kriterion.ArgoMAC.Security.SharedRetained
