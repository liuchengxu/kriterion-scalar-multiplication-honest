import Proof.Privacy.Source.SharedRandomnessSource
import Proof.Privacy.Source.FullSourceTape

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- The retained tape uses the same three shared slots as the actual construction. -/
abbrev SharedMaskRetainedTape [FieldCertificate] [GroupCertificate] :=
  {retained : MaskRetainedTape //
    Shared.expandOracle (Shared.restrictOracle retained.2.2.2.fixedKeyOracle) =
      retained.2.2.2.fixedKeyOracle}

/-- The actual shared tape retains its oracle constraint after the source split. -/
def sharedMaskRetainedTape [FieldCertificate] [GroupCertificate] (randomness : Shared.Randomness) :
    SharedMaskRetainedTape := ⟨maskRetainedTape randomness.val, randomness.property⟩

/-- The retained projection keeps the original fixed oracle. -/
theorem maskRetainedTape_fixedOracle [FieldCertificate] [GroupCertificate]
    (randomness : Garbling.Randomness) :
    (maskRetainedTape randomness).2.2.2.fixedKeyOracle = randomness.fixedKeyOracle := rfl

/-- The full-source reconstruction keeps the retained fixed oracle. -/
theorem fullSourceTape_fixedOracle [FieldCertificate] [GroupCertificate]
    (retained : MaskRetainedTape)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) :
    (fullSourceTape retained full).1.fixedKeyOracle = retained.2.2.2.fixedKeyOracle := by
  have preserved := congrArg (fun retained : MaskRetainedTape => retained.2.2.2.fixedKeyOracle)
    (fullSourceTape_retained retained full)
  simpa only [maskRetainedTape_fixedOracle] using preserved

/-- Every reconstructed shared source satisfies the actual oracle constraint. -/
def sharedFullSourceTape [FieldCertificate] [GroupCertificate]
    (retained : SharedMaskRetainedTape)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) :
    Shared.Randomness × FullCircuitSource :=
  (⟨(fullSourceTape retained.val full).1, by
    rw [fullSourceTape_fixedOracle]
    exact retained.property⟩, (fullSourceTape retained.val full).2)

/-- The source reconstruction recovers the original constrained tape and tag. -/
theorem sharedFullSourceTape_original [FieldCertificate] [GroupCertificate]
    (randomness : Shared.Randomness) (tag : FullCircuitSource) :
    sharedFullSourceTape (sharedMaskRetainedTape randomness)
      (tag.1, sharedCircuitHashRest randomness.val tag.2) = (randomness, tag) := by
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst (fullSourceTape_original randomness.val tag)
  · change (fullSourceTape (maskRetainedTape randomness.val)
      (tag.1, sharedCircuitHashRest randomness.val tag.2)).2 = tag
    exact congrArg Prod.snd (fullSourceTape_original randomness.val tag)

/-- The source split is an equivalence on the actual three-slot tape. -/
def sharedFullSourceEquiv [FieldCertificate] [GroupCertificate] :
    (Shared.Randomness × FullCircuitSource) ≃
      SharedMaskRetainedTape × ((RawCircuitGate → FullHashLift) × CircuitHashRest) where
  toFun sample := (sharedMaskRetainedTape sample.1,
    sample.2.1, sharedCircuitHashRest sample.1.val sample.2.2)
  invFun sample := sharedFullSourceTape sample.1 sample.2
  left_inv sample := sharedFullSourceTape_original sample.1 sample.2
  right_inv sample := by
    apply Prod.ext
    · apply Subtype.ext
      exact fullSourceTape_retained sample.1.val sample.2
    · exact fullSourceTape_source sample.1.val sample.2

/-- The reconstructed source keeps its exact retained data. -/
theorem sharedFullSourceTape_retained [FieldCertificate] [GroupCertificate]
    (retained : SharedMaskRetainedTape)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) :
    sharedMaskRetainedTape (sharedFullSourceTape retained full).1 = retained := by
  apply Subtype.ext
  exact fullSourceTape_retained retained.val full

/-- The reconstructed shared tape retains the complete source coordinates. -/
theorem sharedFullSourceTape_source [FieldCertificate] [GroupCertificate]
    (retained : SharedMaskRetainedTape)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) :
    ((sharedFullSourceTape retained full).2.1,
      sharedCircuitHashRest (sharedFullSourceTape retained full).1.val
        (sharedFullSourceTape retained full).2.2) = full :=
  fullSourceTape_source retained.val full

end
end Kriterion.ArgoMAC.Security
