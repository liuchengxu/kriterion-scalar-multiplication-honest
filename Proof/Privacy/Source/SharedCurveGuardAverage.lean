import Proof.Privacy.Source.SharedCurveGoodMass
import Proof.Privacy.Collision.SharedCurvePadGuard
import Proof.Privacy.Source.SharedRetainedAverage

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section
set_option maxRecDepth 2048
local instance curveGuardAverageKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveGuardAverageKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
attribute [local instance] instFintypeRawCircuitGate_1

/-- The invalid source retains distinct linking pads with the same relative count. -/
theorem curveHidden_guard_average_ge [Fintype Block]
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
    (1 - ((54691280 + (364 * history.length : Nat)) / (2 : ENNReal) ^ 128)) *
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
              (Shared.expandOracle fixedOracle) ∧ PermutationTranscriptMatches fixedOracle history ∧ ¬ curveHiddenPadBad context key} := by
  apply retained_average_ge (PMF.uniformOfFintype InputMacKey)
    {key | (sharedCrossBranchCollision ((context.curveHidden key).pointBranches hidden)
        ((context.curveHidden key).curveBranches hidden) (curveUnused key) ∨
      sharedPrequeryLabelCollision history (curveHiddenQueryUses context hidden history) key) ∨
        curveHiddenPadBad context key}
  · exact curveHidden_guard_failure_mass_le context hidden history
  · intro key good
    have clean := not_or.mp good
    have goodSource := not_or.mp clean.1
    simp only [clean.2, not_false_eq_true, and_true]
    exact (curveHidden_good_mass_eq context hidden anchor pointGood reference history compatible active key
      goodSource.1 goodSource.2).symm.le

end
end Kriterion.ArgoMAC.Security.SharedRetained
