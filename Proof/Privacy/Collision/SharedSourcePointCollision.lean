import Proof.Privacy.Collision.SharedConcreteRetainedFlags
import Proof.Privacy.Source.SharedRetainedContext

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
noncomputable section

/-- This offset keeps the actual source block and the paper digit tweak. -/
def sharedSourcePointOffset (source : CircuitMaskSample) (row : Fin outputMacCount)
    (family : PointGateFamily) (bit : Fin coordinateBitCount) (slot : Pipeline.FixedKeySlot) : Block :=
  circuitSourceOffset source (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
    (pointRawGate row family bit) slot ^^^ (rawCircuitLocation (pointRawGate row family bit)).tweak

/-- This event checks the point-row collisions directly in the retained source. -/
def sharedSourcePointCollision (source : CircuitMaskSample) : Prop :=
  ∃ (family : PointGateFamily) (bit : Fin coordinateBitCount)
      (slot : Pipeline.FixedKeySlot) (pair : PointRowPair),
    sharedSourcePointOffset source pair.lower family bit slot =
      sharedSourcePointOffset source pair.1 family bit slot

/-- The reconstructed source keeps the exact point offset from its public sample. -/
theorem sharedSourcePointOffset_reconstructed (sample : PublicSample) (mask : BaseField)
    (rows : Fin outputMacCount → Coordinates.Rows) (input : AffineInput) (curveTarget : BaseField)
    (targets : Fin outputMacCount → HomogeneousValue) (row : Fin outputMacCount)
    (family : PointGateFamily) (bit : Fin coordinateBitCount) (slot : Pipeline.FixedKeySlot) :
    sharedSourcePointOffset (reconstructedCircuitSource sample mask rows input curveTarget targets) row family bit slot =
      pointBranchOffset row (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).1
        (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).2 (rows row) input (targets row) family bit slot := by
  unfold sharedSourcePointOffset
  rw [reconstructedCircuitSource_pointOffset]
  rcases family with gate | (gate | gate) <;> rfl

/-- The source split preserves the point-row collision event exactly. -/
theorem sharedSourcePointCollision_split (bridge mask : BaseField) (rows : Rows)
    (sparse : ∀ row, SparseRow (rows.get row)) (input : AffineInput) (sample : PublicSample) :
    sharedSourcePointCollision (circuitMaskSampleSplit bridge mask rows input sample).2 ↔
      retainedSourceBirthday sample rows input := by
  rw [← reconstructedCircuitSource_eq_split bridge mask rows sparse input sample]
  simp only [sharedSourcePointCollision, sharedSourcePointOffset_reconstructed,
    retainedSourceBirthday, pointBranchCollision]

/-- The retained context uses the same point offsets as its complete source. -/
theorem sharedSourcePointOffset_context (context : SharedRetained.Context) (hidden : HiddenPublicSample)
    (row : Fin outputMacCount) (family : PointGateFamily) (bit : Fin coordinateBitCount)
    (slot : Pipeline.FixedKeySlot) :
    sharedSourcePointOffset (context.source hidden) row family bit slot =
      pointBranchOffset row (context.visible.2 row) (hidden.2 row) (context.rows row)
        context.input (context.targets row) family bit slot :=
  SharedRetained.point_source_offset context hidden row family bit slot

/-- The retained context guard is the direct source collision guard. -/
theorem sharedSourcePointCollision_context (context : SharedRetained.Context) (hidden : HiddenPublicSample) :
    sharedSourcePointCollision (context.source hidden) ↔
      pointBranchCollision context.visible.2 context.rows context.input context.targets hidden.2 := by
  simp only [sharedSourcePointCollision, sharedSourcePointOffset_context, pointBranchCollision]

/-- The tag guard tests the exact direct collision event in its decoded source. -/
theorem sharedSourcePointCollision_retained [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : OutputKeys) (input : AffineInput)
    (tag : FullCircuitSource) (key : InputMacKey) :
    sharedSourcePointCollision (retainedFullSource rest tag) ↔
      let retained := SharedRetained.retainedSourceContext rest keys input tag key
      pointBranchCollision retained.1.visible.2 retained.1.rows retained.1.input retained.1.targets retained.2.2 := by
  have law := sharedSourcePointCollision_context
    (SharedRetained.retainedSourceContext rest keys input tag key).1
    (SharedRetained.retainedSourceContext rest keys input tag key).2
  rw [SharedRetained.retainedSourceContext_source] at law
  exact law

end
end Kriterion.ArgoMAC.Security
