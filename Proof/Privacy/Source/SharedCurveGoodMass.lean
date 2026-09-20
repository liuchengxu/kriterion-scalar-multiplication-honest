import Proof.Privacy.Source.SharedCurvePostquery

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section
attribute [local instance] instFintypeRawCircuitGate_1

/-- A good hidden sample gives the same exact curve-only source factor. -/
theorem curveHidden_good_mass_eq [Fintype Block]
    (context : Context) (hidden : HiddenPublicSample) (anchor : InputMacKey)
    (pointGood : ¬ pointBranchCollision context.visible.2 context.rows context.input context.targets hidden.2)
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (compatible : PermutationTranscriptMatches reference history)
    (active : ∀ gate slot,
      sharedCurveSlot (Shared.fixedIndex (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) = true →
      rawSlotBranch slot = inputSelectedLabelBit context.input (circuitGateWire gate) →
      let record := ((context.curveHidden anchor).gates (hidden, curveUnused anchor) gate).slotRecord slot
      reference.permutation (Shared.fixedIndex record.index) record.domain = record.range)
    (key : InputMacKey)
    (crossing : ¬ sharedCrossBranchCollision ((context.curveHidden key).pointBranches hidden)
      ((context.curveHidden key).curveBranches hidden) (curveUnused key))
    (fresh : ¬ sharedPrequeryLabelCollision history (curveHiddenQueryUses context hidden history) key) :
    (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
      {fixedOracle | RawGarblingMatches ((context.curveHidden key).gates (hidden, curveUnused key))
        (Shared.expandOracle fixedOracle) ∧ PermutationTranscriptMatches fixedOracle history} =
    ∏ index : Shared.FixedKeyIndex,
        ((Fintype.card Block - (sharedCircuitBucketSize index +
          Fintype.card (ResidualQueryDomain history
            (sharedCurveDomains ((context.curveHidden anchor).gates (hidden, curveUnused anchor))
              (sharedCircuitSelected context.input)) index))).factorial : ENNReal) /
                (Fintype.card Block).factorial := by
  have sourceGood : ¬ (context.curveHidden key).collision (hidden, curveUnused key) :=
    fun bad => bad.elim pointGood crossing
  have sampleActive :
      let gates := (context.curveHidden key).gates (hidden, curveUnused key)
      ∀ index, sharedCurveSlot index = true →
        ∀ use : SharedActiveUse gates index (sharedCircuitSelected context.input index),
          reference.permutation index (sharedRawBucketDomain gates index use.1) =
            sharedRawBucketRange gates index use.1 := by
    dsimp only
    intro index curve use
    have indexed : Shared.fixedIndex (fixedKeyIndex (rawCircuitLocation use.1.1.1)
      (rawCircuitWindow use.1.1.1) use.1.1.2) = index := use.1.2
    have selected := use.2.trans ((congrArg (sharedCircuitSelected context.input) indexed).symm.trans
      (sharedCircuitSelected_wire context.input use.1.1.1 use.1.1.2))
    have curveGate : sharedCurveSlot (Shared.fixedIndex (fixedKeyIndex (rawCircuitLocation use.1.1.1)
        (rawCircuitWindow use.1.1.1) use.1.1.2)) = true := by rw [indexed]; exact curve
    have result := active use.1.1.1 use.1.1.2 curveGate selected
    dsimp only at result
    rw [curveHidden_active_record context hidden anchor key use.1.1.1 use.1.1.2 curveGate selected] at result
    change reference.permutation (Shared.fixedIndex (fixedKeyIndex _ _ use.1.1.2)) _ = _ at result
    rw [use.1.2] at result
    exact result
  have mass := curveHidden_postquery_mass context hidden key sourceGood reference history compatible fresh sampleActive
  dsimp only at mass
  rw [curveHidden_domains_stable context hidden key anchor] at mass
  have count (index : Shared.FixedKeyIndex) :
      Fintype.card (SharedRawBucketUse ((context.curveHidden key).gates (hidden, curveUnused key)) index) =
        sharedCircuitBucketSize index := by
    have card := sharedCircuitBucket_card
      (fun gate => ⟨(context.curveHidden key).gateLabel (curveUnused key) gate false,
        (context.curveHidden key).gateLabel (curveUnused key) gate true⟩)
      (circuitSourceSlope ((context.curveHidden key).source hidden)) ((context.curveHidden key).lifts hidden)
      (circuitSourceTable ((context.curveHidden key).source hidden)) index
    convert card using 1
    exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
  simp_rw [count] at mass
  exact mass

end
end Kriterion.ArgoMAC.Security.SharedRetained
