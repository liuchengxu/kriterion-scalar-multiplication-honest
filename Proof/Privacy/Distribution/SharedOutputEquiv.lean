import Proof.Privacy.Distribution.SharedTapeDistribution
import Proof.Privacy.Distribution.AdaptiveOutputDistribution

namespace Kriterion.ArgoMAC.Security
open BN254 FieldMacToECMac
noncomputable section
attribute [local instance] Classical.propDecidable vectorFintype rowRandomnessFintype
  xRandomnessFintype yRandomnessFintype zRandomnessFintype

/-- The row source retains the actual shared fixed oracle. -/
abbrev SharedOutputRowSource [FieldCertificate] := {source : OutputRowSource //
  Shared.expandOracle (Shared.restrictOracle source.2.2.2.2.fixedKeyOracle) = source.2.2.2.2.fixedKeyOracle}

/-- The source split changes only the point and row representations. -/
def sharedOutputRowSourceEquiv [FieldCertificate] :
    (OffsetRandomness × SharedOffsetRest) ≃ SharedOutputRowSource where
  toFun source := ⟨outputRowSourceEquiv (source.1, source.2.val), source.2.property⟩
  invFun source :=
    let original := outputRowSourceEquiv.symm source.val
    (original.1, ⟨original.2, source.property⟩)
  left_inv source := by
    have restored := outputRowSourceEquiv.symm_apply_apply (source.1, source.2.val)
    apply Prod.ext
    · exact congrArg (fun pair : OffsetRandomness × GarblingOffsetRest => pair.1) restored
    · apply Subtype.ext
      exact congrArg (fun pair : OffsetRandomness × GarblingOffsetRest => pair.2) restored
  right_inv source := by
    apply Subtype.ext
    exact outputRowSourceEquiv.apply_symm_apply source.val

instance sharedOutputRowSourceNonempty [FieldCertificate] [GroupCertificate] : Nonempty SharedOutputRowSource :=
  Nonempty.map sharedOutputRowSourceEquiv inferInstance

/-- Scale normalization leaves the actual fixed oracle unchanged. -/
theorem selectedOutputNormalization_fixed [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (input : AffineInput) (randomness : Garbling.Randomness) :
    (selectedOutputNormalization scalar input randomness).fixedKeyOracle = randomness.fixedKeyOracle := by
  have retained := congrArg (fun rest : OutputRowRest => rest.2.2.fixedKeyOracle)
    (selectedOutputNormalization_rest scalar input randomness)
  exact retained

/-- The scale equivalence restricts to the actual shared tape. -/
def sharedSelectedOutputNormalization [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (input : AffineInput) : Shared.Randomness ≃ Shared.Randomness :=
  (selectedOutputNormalization scalar input).subtypeEquiv (fun randomness => by
    rw [selectedOutputNormalization_fixed])

/-- The point reindex preserves every retained shared tape value. -/
def sharedSelectedOutputReindex [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    (scalar : ScalarField) (input : AffineInput) :
    (OffsetRandomness × SharedOffsetRest) ≃ (OffsetRandomness × SharedOffsetRest) :=
  match decodePoint input with
  | none => Equiv.refl _
  | some point => Equiv.prodCongr (construction.offsetEquiv scalar point) (Equiv.refl _)

/-- The shared point reindex has the original deterministic point effect. -/
theorem sharedSelectedOutputReindex_value [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    (scalar : ScalarField) (input : AffineInput) (source : OffsetRandomness × SharedOffsetRest) :
    ((sharedSelectedOutputReindex scalar input source).1,
      (sharedSelectedOutputReindex scalar input source).2.val) =
      selectedOutputReindex scalar input (source.1, source.2.val) := by
  cases decoded : decodePoint input <;>
    simp only [sharedSelectedOutputReindex, selectedOutputReindex, decoded] <;> rfl

/-- The shared point reindex retains the source view that controls the adaptive choice. -/
theorem sharedSelectedOutputReindex_rest [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    (scalar : ScalarField) (input : AffineInput) (source : OffsetRandomness × SharedOffsetRest) :
    (sharedSelectedOutputReindex scalar input source).2 = source.2 := by
  unfold sharedSelectedOutputReindex
  split <;> rfl

end
end Kriterion.ArgoMAC.Security
