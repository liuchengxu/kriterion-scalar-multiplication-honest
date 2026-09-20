import Proof.Privacy.Source.SharedLinkedSource

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography
noncomputable section

/-- This retained view gives each source the paper's actual selected row targets. -/
def contextFromSource (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows)
    (input : AffineInput) (source : CircuitMaskSample)
    (curveLabels pointLabels pads : EncPRF.PermutationIndex → Block) : Context × HiddenPublicSample :=
  let sample := (circuitMaskSampleSplit bridgeKey mask rows input).symm (0, source)
  let split := PublicSample.visibleHiddenEquiv sample
  (⟨split.1, mask, fun row => rows.get row, input,
    bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2),
    fun row => (FieldMacToECMac.evaluateRowsCubic rows input).get row, curveLabels, pointLabels, pads⟩, split.2)

/-- The retained view reconstructs every original source field exactly. -/
theorem contextFromSource_source (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows)
    (sparse : ∀ row, FieldMacToECMac.SparseRow (rows.get row))
    (input : AffineInput) (source : CircuitMaskSample)
    (curveLabels pointLabels pads : EncPRF.PermutationIndex → Block) :
    let retained := contextFromSource bridgeKey mask rows input source curveLabels pointLabels pads
    retained.1.source retained.2 = source := by
  dsimp only [contextFromSource, Context.source]
  rw [Equiv.symm_apply_apply, reconstructedCircuitSource_eq_split bridgeKey mask rows sparse input]
  exact congrArg Prod.snd ((circuitMaskSampleSplit bridgeKey mask rows input).apply_symm_apply (0, source))

/-- The retained view also keeps every complete source hash lift. -/
theorem contextFromSource_lifts (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows)
    (sparse : ∀ row, FieldMacToECMac.SparseRow (rows.get row))
    (input : AffineInput) (source : CircuitMaskSample)
    (curveLabels pointLabels pads : EncPRF.PermutationIndex → Block) :
    let retained := contextFromSource bridgeKey mask rows input source curveLabels pointLabels pads
    retained.1.lifts retained.2 = fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate) := by
  dsimp only
  unfold Context.lifts
  rw [contextFromSource_source bridgeKey mask rows sparse input]

end
end Kriterion.ArgoMAC.Security.SharedRetained
