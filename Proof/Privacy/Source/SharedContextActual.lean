import Proof.Privacy.Source.SharedContextFromSource

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography
noncomputable section

/-- This context uses the actual input key and its encryption shifts. -/
def actualSourceContext (oracle : SimulatorOracleCoin) (bridgeKey mask : BaseField)
    (rows : FieldMacToECMac.Rows) (input : AffineInput) (source : CircuitMaskSample)
    (key : InputMacKey) : Context × HiddenPublicSample :=
  contextFromSource bridgeKey mask rows input source
    (fun index => inputKeyLabel key index (inputSelectedLabelBit input index))
    (fun index => inputKeyLabel (EncPRF.transformKey oracle.encOracle
      (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key) index (inputSelectedLabelBit input index))
    (fun index => evenMansour (oracle.encOracle.permutation index)
      (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) (!(inputSelectedLabelBit input index)))

/-- The actual context satisfies both encryption links. -/
theorem actualSourceContext_linked (oracle : SimulatorOracleCoin) (bridgeKey mask : BaseField)
    (rows : FieldMacToECMac.Rows) (input : AffineInput) (source : CircuitMaskSample)
    (key : InputMacKey) :
    (actualSourceContext oracle bridgeKey mask rows input source key).1.Linked oracle bridgeKey := by
  intro index
  exact ⟨linkedLabel_fixedShift oracle bridgeKey key index (inputSelectedLabelBit input index), rfl⟩

/-- The unused labels reconstruct the original input key. -/
theorem actualSourceContext_key (oracle : SimulatorOracleCoin) (bridgeKey mask : BaseField)
    (rows : FieldMacToECMac.Rows) (input : AffineInput) (source : CircuitMaskSample)
    (key : InputMacKey) :
    (actualSourceContext oracle bridgeKey mask rows input source key).1.curveKey
      (fun index => inputKeyLabel key index (!(inputSelectedLabelBit input index))) = key := by
  exact (selectedKeyLabelsEquiv (inputSelectedLabelBit input)).symm_apply_apply key

/-- The actual context reconstructs the complete source. -/
theorem actualSourceContext_source (oracle : SimulatorOracleCoin) (bridgeKey mask : BaseField)
    (rows : FieldMacToECMac.Rows) (sparse : ∀ row, FieldMacToECMac.SparseRow (rows.get row))
    (input : AffineInput) (source : CircuitMaskSample) (key : InputMacKey) :
    let retained := actualSourceContext oracle bridgeKey mask rows input source key
    retained.1.source retained.2 = source := by
  exact contextFromSource_source bridgeKey mask rows sparse input source _ _ _

/-- The actual context keeps each complete hash lift. -/
theorem actualSourceContext_lifts (oracle : SimulatorOracleCoin) (bridgeKey mask : BaseField)
    (rows : FieldMacToECMac.Rows) (sparse : ∀ row, FieldMacToECMac.SparseRow (rows.get row))
    (input : AffineInput) (source : CircuitMaskSample) (key : InputMacKey) :
    let retained := actualSourceContext oracle bridgeKey mask rows input source key
    retained.1.lifts retained.2 = fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate) := by
  exact contextFromSource_lifts bridgeKey mask rows sparse input source _ _ _

end
end Kriterion.ArgoMAC.Security.SharedRetained
