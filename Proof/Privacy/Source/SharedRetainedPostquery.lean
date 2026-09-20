import Proof.Privacy.Source.SharedRetainedMass
import Proof.Privacy.Programming.SharedScheduleCounts
import Proof.Privacy.Collision.SharedHiddenQueryBound

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section
set_option maxRecDepth 2048
attribute [local instance] instFintypeRawCircuitGate_1

/-- The shared bucket selects the same actual input wire as every source gate. -/
theorem sharedCircuitSelected_wire (input : AffineInput) (gate : RawCircuitGate)
    (slot : Pipeline.FixedKeySlot) :
    sharedCircuitSelected input (Shared.fixedIndex
      (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) =
        inputSelectedLabelBit input (circuitGateWire gate) := by
  rcases gate with ⟨family, position⟩ | ⟨row, family⟩
  · fin_cases family <;> simp [sharedCircuitSelected, Shared.fixedIndex, fixedKeyIndex, rawCircuitLocation, rawCircuitWindow, Pipeline.FixedKeyLocation.kind, circuitBucketInputBit, inputSelectedLabelBit, circuitGateWire, Nat.mod_eq_of_lt position.isLt]
  · rcases family with ⟨family, position⟩ | (⟨family, position⟩ | ⟨family, position⟩) <;>
      fin_cases family <;> simp [sharedCircuitSelected, Shared.fixedIndex, fixedKeyIndex, rawCircuitLocation, rawCircuitWindow, Pipeline.FixedKeyLocation.kind, circuitBucketInputBit, inputSelectedLabelBit, circuitGateWire, Nat.mod_eq_of_lt position.isLt]

namespace SharedRetained

/-- The actual retained source has this exact post-query mass, including active replays. -/
theorem linked_postquery_mass [Fintype Block]
    (context : Context) (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (linked : context.Linked oracle bridgeKey)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (good : ¬ context.collision sample)
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (compatible : PermutationTranscriptMatches reference history)
    (fresh : ¬ sharedHiddenQueryCollision history
      (sharedSourcePrequeryUses oracle bridgeKey (context.source sample.1)
        (context.lifts sample.1) history) sample.2)
    (active :
      let gates := sourceGatePrescription (context.source sample.1)
        (EncPRF.transformKey oracle.encOracle (EncPRF.whiteningKeys oracle.hashOracle bridgeKey)
          (context.curveKey sample.2)) (context.curveKey sample.2) (context.lifts sample.1)
      ∀ index, ∀ use : SharedActiveUse gates index (sharedCircuitSelected context.input index),
        reference.permutation index (sharedRawBucketDomain gates index use.1) =
          sharedRawBucketRange gates index use.1) :
    let gates := sourceGatePrescription (context.source sample.1)
      (EncPRF.transformKey oracle.encOracle (EncPRF.whiteningKeys oracle.hashOracle bridgeKey)
        (context.curveKey sample.2)) (context.curveKey sample.2) (context.lifts sample.1)
    (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
      {fixedOracle | RawGarblingMatches gates (Shared.expandOracle fixedOracle) ∧
        PermutationTranscriptMatches fixedOracle history} =
      ∏ index : Shared.FixedKeyIndex,
        ((Fintype.card Block - (Fintype.card (SharedRawBucketUse gates index) +
          Fintype.card (ResidualQueryDomain history
            (sharedActiveDomains gates (sharedCircuitSelected context.input)) index))).factorial : ENNReal) /
            (Fintype.card Block).factorial := by
  dsimp only
  apply sharedActiveTranscript_mass _ (sharedCircuitSelected context.input) reference history compatible
  · intro index
    exact (linked_assignments_injective context oracle bridgeKey linked sample good index).1
  · intro index
    exact (linked_assignments_injective context oracle bridgeKey linked sample good index).2
  · exact active
  · intro index use hidden query
    have wire : sharedCircuitSelected context.input index =
        inputSelectedLabelBit context.input (circuitGateWire use.1.1) := by
      exact (congrArg (sharedCircuitSelected context.input) use.2).symm.trans
        (sharedCircuitSelected_wire context.input use.1.1 use.1.2)
    have hiddenWire : rawSlotBranch use.1.2 ≠
        inputSelectedLabelBit context.input (circuitGateWire use.1.1) := by
      rwa [wire] at hidden
    have rawFresh := sharedSourceHiddenQueryCollision_false_fresh oracle bridgeKey context sample.1
      sample.2 history fresh use.1.1 use.1.2 hiddenWire
    obtain ⟨record, member, sameIndex, sameDomain⟩ := query.1.2
    have tested := rawFresh record member (sameIndex.trans use.2.symm)
    have answer := compatible record member
    rw [sameIndex, sameDomain] at answer
    constructor
    · intro equal
      exact tested.1 (sameDomain.trans equal.symm)
    · intro equal
      exact tested.2 (answer.symm.trans equal.symm)

/-- The post-query exclusions retain the full hidden-source distribution. -/
theorem postquery_failure_mass_le [Fintype Block]
    (context : Context) (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block)) :
    law.toOuterMeasure {sample | context.collision sample ∨ sharedHiddenQueryCollision history
      (sharedSourcePrequeryUses oracle bridgeKey (context.source sample.1)
        (context.lifts sample.1) history) sample.2} ≤
      ((248222021716 / 1000) + (364 * history.length : Nat)) / (2 : ENNReal) ^ 128 := by
  have card : Fintype.card Block = 2 ^ 128 :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  have queryBound : law.toOuterMeasure {sample | sharedHiddenQueryCollision history
      (sharedSourcePrequeryUses oracle bridgeKey (context.source sample.1)
        (context.lifts sample.1) history) sample.2} ≤
        (364 * history.length : Nat) / (2 : ENNReal) ^ 128 := by
    unfold law
    rw [PMF.toOuterMeasure_bind_apply]
    calc
      _ ≤ ∑' hidden, (PMF.uniformOfFintype HiddenPublicSample) hidden *
          ((364 * history.length : Nat) / (2 : ENNReal) ^ 128) := by
        apply ENNReal.tsum_le_tsum
        intro hidden
        apply mul_le_mul_right
        rw [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
        have bound := sharedHiddenQueryCollision_mass_le history
          (sharedSourcePrequeryUses oracle bridgeKey (context.source hidden) (context.lifts hidden) history)
        simpa only [card, Nat.cast_pow, Nat.cast_ofNat] using bound
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  apply (MeasureTheory.measure_union_le (μ := law.toOuterMeasure)
    {sample | context.collision sample}
    {sample | sharedHiddenQueryCollision history
      (sharedSourcePrequeryUses oracle bridgeKey (context.source sample.1)
        (context.lifts sample.1) history) sample.2}).trans
  exact (add_le_add (collision_mass_le context) queryBound).trans_eq (ENNReal.add_div ..).symm

end SharedRetained
end
end Kriterion.ArgoMAC.Security
