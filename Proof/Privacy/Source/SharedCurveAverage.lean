import Proof.Privacy.Source.SharedCurveGoodMass
import Proof.Privacy.Source.SharedRetainedAverage

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section
local instance curveAverageKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveAverageKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
attribute [local instance] instFintypeRawCircuitGate_1

/-- The two hidden arrays give the invalid branch its exact relative source loss. -/
theorem curveHidden_average_ge [Fintype Block]
    (context : Context) (hidden : HiddenPublicSample) (anchor : InputMacKey)
    (pointGood : ¬ pointBranchCollision context.visible.2 context.rows context.input context.targets hidden.2)
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (compatible : PermutationTranscriptMatches reference history)
    (active : ∀ gate slot,
      sharedCurveSlot (Shared.fixedIndex (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) = true →
      rawSlotBranch slot = inputSelectedLabelBit context.input (circuitGateWire gate) →
      let record := ((context.curveHidden anchor).gates (hidden, curveUnused anchor) gate).slotRecord slot
      reference.permutation (Shared.fixedIndex record.index) record.domain = record.range) :
    (1 - ((54690772 + (364 * history.length : Nat)) / (2 : ENNReal) ^ 128)) *
      (∏ index : Shared.FixedKeyIndex,
        ((Fintype.card Block - (sharedCircuitBucketSize index +
          Fintype.card (ResidualQueryDomain history
            (sharedCurveDomains ((context.curveHidden anchor).gates (hidden, curveUnused anchor))
              (sharedCircuitSelected context.input)) index))).factorial : ENNReal) /
                (Fintype.card Block).factorial) ≤
      ∑' key, (PMF.uniformOfFintype InputMacKey) key *
        (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
          {fixedOracle |
            RawGarblingMatches ((context.curveHidden key).gates (hidden, curveUnused key))
              (Shared.expandOracle fixedOracle) ∧ PermutationTranscriptMatches fixedOracle history} := by
  apply retained_average_ge (PMF.uniformOfFintype InputMacKey)
    {key | sharedCrossBranchCollision ((context.curveHidden key).pointBranches hidden)
        ((context.curveHidden key).curveBranches hidden) (curveUnused key) ∨
      sharedPrequeryLabelCollision history (curveHiddenQueryUses context hidden history) key}
  · exact curveHidden_failure_mass_le context hidden history
  · intro key good
    have clean := not_or.mp good
    exact (curveHidden_good_mass_eq context hidden anchor pointGood reference history compatible active key
      clean.1 clean.2).symm.le

end
end Kriterion.ArgoMAC.Security.SharedRetained
