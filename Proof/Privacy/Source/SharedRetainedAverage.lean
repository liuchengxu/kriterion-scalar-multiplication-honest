import Proof.Privacy.Source.SharedStableActiveRecords
import Proof.Privacy.Source.SharedScheduleRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section

/-- A retained constant lower bound survives the average over source samples. -/
theorem retained_average_ge {Source : Type} (samples : PMF Source)
    (bad : Set Source) (error factor : ENNReal) (weight : Source → ENNReal)
    (badMass : samples.toOuterMeasure bad ≤ error)
    (retained : ∀ sample, sample ∉ bad → factor ≤ weight sample) :
    (1 - error) * factor ≤ ∑' sample, samples sample * weight sample := by
  classical
  have total : samples.toOuterMeasure badᶜ + samples.toOuterMeasure bad = 1 := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
    convert samples.tsum_coe using 1
    apply tsum_congr
    intro sample
    by_cases member : sample ∈ bad <;> simp [Set.indicator, member]
  have kept : 1 - error ≤ samples.toOuterMeasure badᶜ := by
    apply tsub_le_iff_right.mpr
    rw [← total]
    exact add_le_add_right badMass _
  apply (mul_le_mul_left kept factor).trans
  rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro sample
  by_cases member : sample ∈ bad
  · simp [Set.indicator, member]
  · simpa only [Set.indicator_of_mem (show sample ∈ badᶜ from member)] using
      mul_le_mul_right (retained sample member) (samples sample)

namespace SharedRetained

/-- This product keeps the complete source count and the residual external queries. -/
def Context.transcriptFactor [Fintype Block] (context : Context)
    (anchor : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (history : List (PermutationRecord Shared.FixedKeyIndex Block)) : ENNReal :=
  ∏ index : Shared.FixedKeyIndex,
    ((Fintype.card Block - (sharedCircuitBucketSize index +
      Fintype.card (ResidualQueryDomain history
        (sharedActiveDomains (context.gates anchor) (sharedCircuitSelected context.input)) index))).factorial : ENNReal) /
      (Fintype.card Block).factorial

/-- The unused-label average charges cross-branch and post-query exclusions once. -/
theorem linked_unusedLabel_average_ge [Fintype Block]
    (context : Context) (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (linked : context.Linked oracle bridgeKey) (hidden : HiddenPublicSample)
    (anchor : EncPRF.PermutationIndex → Block)
    (pointGood : ¬ pointBranchCollision context.visible.2 context.rows context.input context.targets hidden.2)
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (compatible : PermutationTranscriptMatches reference history)
    (active : ∀ gate slot,
      rawSlotBranch slot = inputSelectedLabelBit context.input (circuitGateWire gate) →
      let record := (context.gates (hidden, anchor) gate).slotRecord slot
      reference.permutation (Shared.fixedIndex record.index) record.domain = record.range) :
    (1 - ((54690772 + (364 * history.length : Nat)) / (2 : ENNReal) ^ 128)) *
      context.transcriptFactor (hidden, anchor) history ≤
      ∑' labels, (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)) labels *
        (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
          {fixedOracle | RawGarblingMatches (context.gates (hidden, labels)) (Shared.expandOracle fixedOracle) ∧
            PermutationTranscriptMatches fixedOracle history} := by
  apply retained_average_ge (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block))
    {labels | sharedCrossBranchCollision (context.pointBranches hidden) (context.curveBranches hidden) labels ∨
      sharedHiddenQueryCollision history (sharedSourcePrequeryUses oracle bridgeKey (context.source hidden)
        (context.lifts hidden) history) labels}
  · have crossing := sharedCrossBranchCollision_mass_le (context.pointBranches hidden) (context.curveBranches hidden)
    have queries := sharedHiddenQueryCollision_mass_le history
      (sharedSourcePrequeryUses oracle bridgeKey (context.source hidden) (context.lifts hidden) history)
    have card : Fintype.card Block = 2 ^ 128 :=
      (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
    rw [card, Nat.cast_pow, Nat.cast_ofNat] at queries
    apply (MeasureTheory.measure_union_le
      (μ := (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).toOuterMeasure)
      {labels | sharedCrossBranchCollision (context.pointBranches hidden) (context.curveBranches hidden) labels}
      {labels | sharedHiddenQueryCollision history (sharedSourcePrequeryUses oracle bridgeKey
        (context.source hidden) (context.lifts hidden) history) labels}).trans
    exact (add_le_add crossing queries).trans_eq (ENNReal.add_div ..).symm
  · intro labels good
    have clean := not_or.mp good
    have sourceGood : ¬ context.collision (hidden, labels) := fun bad => bad.elim pointGood clean.1
    have sampleActive := active_records_compatible context hidden anchor labels reference active
    rw [linked_gates context oracle bridgeKey linked (hidden, labels)] at sampleActive
    have mass := linked_postquery_mass context oracle bridgeKey linked (hidden, labels) sourceGood
      reference history compatible clean.2 sampleActive
    rw [← linked_gates context oracle bridgeKey linked (hidden, labels)] at mass
    dsimp only at mass
    rw [active_domains_stable context (hidden, labels) (hidden, anchor)] at mass
    have count (index : Shared.FixedKeyIndex) :
        Fintype.card (SharedRawBucketUse (context.gates (hidden, labels)) index) = sharedCircuitBucketSize index := by
      have card := sharedCircuitBucket_card
        (fun gate => ⟨context.gateLabel labels gate false, context.gateLabel labels gate true⟩)
        (circuitSourceSlope (context.source hidden)) (context.lifts hidden)
        (circuitSourceTable (context.source hidden)) index
      convert card using 1
      exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
    simp_rw [count] at mass
    exact mass.symm.le

end SharedRetained

end
end Kriterion.ArgoMAC.Security
