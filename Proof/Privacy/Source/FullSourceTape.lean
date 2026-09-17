import Proof.Privacy.Source.CompleteCurveTransport

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1
  instFintypeCircuitMaskTables instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

/-- The shared full source reconstructs the actual tape and its full tag. -/
def fullSourceTape [FieldCertificate] [GroupCertificate]
    (retained : MaskRetainedTape)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) : Garbling.Randomness × FullCircuitSource :=
  (sharedHashSourceEquiv (RawCircuitGate → FullHashLift)).symm (retained, full)

private theorem sharedFullSource_forward [FieldCertificate] [GroupCertificate]
    (sample : Garbling.Randomness × FullCircuitSource) :
    sharedHashSourceEquiv (RawCircuitGate → FullHashLift) sample =
      (maskRetainedTape sample.1, sample.2.1, sharedCircuitHashRest sample.1 sample.2.2) := rfl

/-- The full source inverse recovers every original randomizer and tag coordinate. -/
theorem fullSourceTape_original [FieldCertificate] [GroupCertificate]
    (randomness : Garbling.Randomness) (tag : FullCircuitSource) :
    fullSourceTape (maskRetainedTape randomness) (tag.1, sharedCircuitHashRest randomness tag.2) =
      (randomness, tag) := by
  exact (sharedHashSourceEquiv (RawCircuitGate → FullHashLift)).symm_apply_apply (randomness, tag)

/-- Every observer has the exact normalized full-source disintegration. -/
theorem fullSourceTape_observation_eq [FieldCertificate] [GroupCertificate] {Observation : Type*}
    (witness : Garbling.Randomness) (parameter : Nat)
    (observe : Garbling.Randomness → FullCircuitSource → PMF Observation) :
    (randomTape witness parameter).bind (fun randomness =>
      (PMF.uniformOfFintype FullCircuitSource).bind (observe randomness)) =
    (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)).bind (fun full =>
      (PMF.uniformOfFintype MaskRetainedTape).bind fun retained =>
        observe (fullSourceTape retained full).1 (fullSourceTape retained full).2) := by
  have law := sharedHashSource_observation_eq witness parameter
    (fun retained full => observe (fullSourceTape retained full).1 (fullSourceTape retained full).2)
  simpa only [fullSourceTape_original] using law

/-- The reconstructed tape retains the exact oracle and row data. -/
theorem fullSourceTape_retained [FieldCertificate] [GroupCertificate]
    (retained : MaskRetainedTape)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) :
    maskRetainedTape (fullSourceTape retained full).1 = retained := by
  have inverse := (sharedHashSourceEquiv (RawCircuitGate → FullHashLift)).apply_symm_apply (retained, full)
  exact congrArg (fun sample => sample.1) inverse

set_option maxHeartbeats 2000000 in
/-- The reconstructed tape and tag have exactly the supplied full source. -/
theorem fullSourceTape_source [FieldCertificate] [GroupCertificate]
    (retained : MaskRetainedTape)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) :
    ((fullSourceTape retained full).2.1,
      sharedCircuitHashRest (fullSourceTape retained full).1 (fullSourceTape retained full).2.2) = full := by
  have inverse : sharedHashSourceEquiv (RawCircuitGate → FullHashLift)
      (fullSourceTape retained full) = (retained, full) :=
    (sharedHashSourceEquiv (RawCircuitGate → FullHashLift)).apply_symm_apply (retained, full)
  rw [sharedFullSource_forward] at inverse
  exact congrArg (fun sample => sample.2) inverse

/-- The decoded source uses the exact reconstructed field randomizers. -/
theorem fullSourceTape_randomizers [FieldCertificate] [GroupCertificate]
    (retained : MaskRetainedTape)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) :
    CircuitSourceRandomizers (decodeFullSource full) (fullSourceTape retained full).1.pointRandomness
      (fullSourceTape retained full).1.curveR1 (fullSourceTape retained full).1.curveR2 := by
  have source := fullSourceTape_source retained full
  have decoded : decodeFullSource full =
      sharedCircuitMaskSample (fullSourceTape retained full).1
        (fun gate => fullSourceHashPair ((fullSourceTape retained full).2.1 gate))
        (fullSourceTape retained full).2.2 := by
    change decodeFullSource full = decodeFullSource
      ((fullSourceTape retained full).2.1,
        sharedCircuitHashRest (fullSourceTape retained full).1 (fullSourceTape retained full).2.2)
    exact congrArg decodeFullSource source.symm
  rw [decoded]
  exact sharedCircuitMaskSample_randomizers (fullSourceTape retained full).1
    (fun gate => fullSourceHashPair ((fullSourceTape retained full).2.1 gate))
    (fullSourceTape retained full).2.2

/-- A complete source uses every original full lift residue. -/
theorem fullSourceTape_residues
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (complete : FullSourceComplete full.1) :
    ∀ gate, circuitSourceField (decodeFullSource full) gate = ((full.1 gate).val : BaseField) := by
  intro gate
  rw [← decodeFullSource_lifts full complete]
  exact ((goodHashLiftSource_field ((circuitMaskHashSplitEquiv (decodeFullSource full)).1 gate)).trans
    (circuitMaskHashSplit_field (decodeFullSource full) gate)).symm

end
end Kriterion.ArgoMAC.Security
