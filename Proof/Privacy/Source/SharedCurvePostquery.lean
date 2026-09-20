import Proof.Privacy.Source.SharedCurveStable
import Proof.Privacy.Collision.SharedCurveLabelMass

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section
attribute [local instance] instFintypeRawCircuitGate_1

/-- The invalid-input source has this exact mass after both public query phases. -/
theorem curveHidden_postquery_mass [Fintype Block]
    (context : Context) (hidden : HiddenPublicSample) (key : InputMacKey)
    (good : ¬ (context.curveHidden key).collision (hidden, curveUnused key))
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (compatible : PermutationTranscriptMatches reference history)
    (fresh : ¬ sharedPrequeryLabelCollision history (curveHiddenQueryUses context hidden history) key)
    (active :
      let gates := (context.curveHidden key).gates (hidden, curveUnused key)
      ∀ index, sharedCurveSlot index = true →
        ∀ use : SharedActiveUse gates index (sharedCircuitSelected context.input index),
          reference.permutation index (sharedRawBucketDomain gates index use.1) =
            sharedRawBucketRange gates index use.1) :
    let gates := (context.curveHidden key).gates (hidden, curveUnused key)
    (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
      {fixedOracle | RawGarblingMatches gates (Shared.expandOracle fixedOracle) ∧
        PermutationTranscriptMatches fixedOracle history} =
      ∏ index : Shared.FixedKeyIndex,
        ((Fintype.card Block - (Fintype.card (SharedRawBucketUse gates index) +
          Fintype.card (ResidualQueryDomain history
            (sharedCurveDomains gates (sharedCircuitSelected context.input)) index))).factorial : ENNReal) /
            (Fintype.card Block).factorial := by
  dsimp only
  apply sharedCurveTranscript_mass _ (sharedCircuitSelected context.input) reference history compatible
  · intro index
    exact (raw_assignments_injective (context.curveHidden key) (hidden, curveUnused key) good index).1
  · intro index
    exact (raw_assignments_injective (context.curveHidden key) (hidden, curveUnused key) good index).2
  · exact active
  · intro index use inactive query
    have indexed : Shared.fixedIndex (fixedKeyIndex (rawCircuitLocation use.1.1)
      (rawCircuitWindow use.1.1) use.1.2) = index := use.2
    have wire : sharedCircuitSelected context.input index =
        inputSelectedLabelBit context.input (circuitGateWire use.1.1) := by
      exact (congrArg (sharedCircuitSelected context.input) indexed).symm.trans
        (sharedCircuitSelected_wire context.input use.1.1 use.1.2)
    have hiddenWire : ¬ (sharedCurveSlot (Shared.fixedIndex
        (fixedKeyIndex (rawCircuitLocation use.1.1) (rawCircuitWindow use.1.1) (.hash 0))) = true ∧
          rawSlotBranch use.1.2 = inputSelectedLabelBit context.input (circuitGateWire use.1.1)) := by
      have kind : sharedCurveSlot (Shared.fixedIndex
          (fixedKeyIndex (rawCircuitLocation use.1.1) (rawCircuitWindow use.1.1) (.hash 0))) =
          sharedCurveSlot index := by
        exact (show sharedCurveSlot (Shared.fixedIndex
          (fixedKeyIndex (rawCircuitLocation use.1.1) (rawCircuitWindow use.1.1) (.hash 0))) =
          sharedCurveSlot (Shared.fixedIndex (fixedKeyIndex (rawCircuitLocation use.1.1)
            (rawCircuitWindow use.1.1) use.1.2)) from rfl).trans (congrArg sharedCurveSlot indexed)
      rwa [kind, ← wire]
    have rawFresh := curveHiddenQuery_false_fresh context hidden key history fresh use.1.1 use.1.2 hiddenWire
    obtain ⟨record, member, sameIndex, sameDomain⟩ := query.1.2
    have tested := rawFresh record member (sameIndex.trans indexed.symm)
    have answer := compatible record member
    rw [sameIndex, sameDomain] at answer
    constructor
    · intro equal
      exact tested.1 (sameDomain.trans equal.symm)
    · intro equal
      exact tested.2 (answer.symm.trans equal.symm)

end
end Kriterion.ArgoMAC.Security.SharedRetained
