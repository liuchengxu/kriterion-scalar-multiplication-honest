import Proof.Privacy.Source.SharedLinkedSource
import Proof.Privacy.Source.SharedTranscriptMass
import Proof.Privacy.Collision.SharedPrequeryBound

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography
open scoped ENNReal
noncomputable section
set_option maxRecDepth 2048
attribute [local instance] instFintypeRawCircuitGate_1

/-- A retained actual source and a fresh transcript give this exact shared permutation mass. -/
theorem linked_transcript_mass [Fintype Block]
    (context : Context) (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (linked : context.Linked oracle bridgeKey)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (good : ¬ context.collision sample)
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (compatible : PermutationTranscriptMatches reference history)
    (fresh : ¬ sharedPrequeryLabelCollision history
      (sharedSourcePrequeryUses oracle bridgeKey (context.source sample.1)
        (context.lifts sample.1) history) (context.curveKey sample.2)) :
    let gates := sourceGatePrescription (context.source sample.1)
      (EncPRF.transformKey oracle.encOracle (EncPRF.whiteningKeys oracle.hashOracle bridgeKey)
        (context.curveKey sample.2)) (context.curveKey sample.2) (context.lifts sample.1)
    (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
      {fixedOracle | RawGarblingMatches gates (Shared.expandOracle fixedOracle) ∧
        PermutationTranscriptMatches fixedOracle history} =
      ∏ index : Shared.FixedKeyIndex,
        ((Fintype.card Block - (sharedCircuitBucketSize index +
          Fintype.card (SharedQueryDomain history index))).factorial : ENNReal) /
            (Fintype.card Block).factorial := by
  dsimp only
  rw [sharedRawGarblingMatches_transcript_mass_of_fresh _ reference history compatible]
  · apply Finset.prod_congr rfl
    intro index _
    have card := sharedCircuitBucket_card
      (circuitGateKey (EncPRF.transformKey oracle.encOracle
        (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) (context.curveKey sample.2))
        (context.curveKey sample.2)) (circuitSourceSlope (context.source sample.1))
        (context.lifts sample.1) (circuitSourceTable (context.source sample.1)) index
    have actualCard : Fintype.card (SharedRawBucketUse
        (sourceGatePrescription (context.source sample.1)
          (EncPRF.transformKey oracle.encOracle (EncPRF.whiteningKeys oracle.hashOracle bridgeKey)
            (context.curveKey sample.2)) (context.curveKey sample.2) (context.lifts sample.1)) index) =
        sharedCircuitBucketSize index := by
      convert card using 1
      exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
    rw [actualCard]
  · intro index
    exact (linked_assignments_injective context oracle bridgeKey linked sample good index).1
  · intro index
    exact (linked_assignments_injective context oracle bridgeKey linked sample good index).2
  · intro index use
    have result := sharedSourcePrequeryCollision_false_fresh oracle bridgeKey
      (context.source sample.1) (context.lifts sample.1) history (context.curveKey sample.2)
      fresh use.1.1 use.1.2
    dsimp only [sharedRawBucketDomain, sharedRawBucketRange]
    change FreshPermutationPair history
      (Shared.fixedIndex (fixedKeyIndex _ _ use.1.2)) _ _ at result
    rw [use.2] at result
    exact result

end
end Kriterion.ArgoMAC.Security.SharedRetained
