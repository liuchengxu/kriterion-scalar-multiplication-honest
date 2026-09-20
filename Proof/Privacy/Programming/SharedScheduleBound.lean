import Proof.Privacy.Programming.SharedScheduleCounts

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 2048
attribute [local irreducible] pipelineGateSchedule scheduleCommands Shared.Simulator.commandRecords
attribute [local instance] instFintypeRawCircuitGate_1 Classical.propDecidable

private theorem activeDomain_card_le [Fintype Block] {Gate : Type} [Fintype Gate]
    (gates : Gate → RawGatePrescription) (selected : Shared.FixedKeyIndex → Bool) (index : Shared.FixedKeyIndex) :
    Fintype.card ↑(sharedActiveDomains gates selected index) ≤ Fintype.card (SharedRawBucketUse gates index) := by
  classical
  let domain : SharedActiveUse gates index (selected index) →
      ↑(sharedActiveDomains gates selected index) := fun use =>
    ⟨sharedRawBucketDomain gates index use.1, use, rfl⟩
  have onto : Function.Surjective domain := by
    rintro ⟨value, use, equal⟩
    exact ⟨use, Subtype.ext equal⟩
  exact (Fintype.card_le_of_surjective domain onto).trans (Fintype.card_le_of_injective
    (fun use : SharedActiveUse gates index (selected index) => use.1) Subtype.val_injective)

/-- Every actual shared schedule fits its full source bucket, even when active domains repeat. -/
theorem sharedCircuitRecords_domainCount_le [Fintype Block]
    (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows) (input : AffineInput)
    (source : CircuitMaskSample) (curveKey pointKey : InputMacKey) (index : Shared.FixedKeyIndex) :
    let sample := circuitMaskSampleGarble bridgeKey mask rows input source
    Fintype.card (SharedQueryDomain (Shared.Simulator.commandRecords (scheduleCommands
      (pipelineGateSchedule sample.curveRequest sample.pointRequests input
        (curveKey.encodeAffine input) (pointKey.encodeAffine input)))) index) ≤
      sharedCircuitBucketSize index := by
  classical
  dsimp only
  let gates := sourceGatePrescription source pointKey curveKey
    (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
  let selected := sharedCircuitSelected input
  have sets := sharedCircuitRecords_domains bridgeKey mask rows input source curveKey pointKey index
  calc
    _ = Fintype.card ↑(sharedActiveDomains gates selected index) := by
      have count := Fintype.card_congr (Equiv.setCongr sets)
      convert count using 1
      exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
    _ ≤ Fintype.card (SharedRawBucketUse gates index) := activeDomain_card_le gates selected index
    _ = sharedCircuitBucketSize index := by
      have count := sharedCircuitBucket_card (circuitGateKey pointKey curveKey) (circuitSourceSlope source)
        (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
        (circuitSourceTable source) index
      convert count using 1
      exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)

end
end Kriterion.ArgoMAC.Security
