import Proof.Privacy.Source.Invalid.InvalidGhostSourceTransport

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section

/-- This frame keeps every retained field except the bridge key and curve mask. -/
abbrev RetainedSourceFrame [FieldCertificate] [GroupCertificate] :=
  ClampedAffineOffsets × (Fin outputMacCount → NonZeroBase) × GarblingOracleData

/-- This equivalence separates the exact retained key and mask. -/
def retainedFrameEquiv [FieldCertificate] [GroupCertificate] :
    MaskRetainedTape ≃ RetainedSourceFrame × (BaseField × NonZeroBase) where
  toFun retained := ((retained.1, retained.2.1, retained.2.2.2), retained.2.2.1)
  invFun sample := (sample.1.1, sample.1.2.1, sample.2, sample.1.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

instance retainedSourceFrameNonempty [FieldCertificate] [GroupCertificate] : Nonempty RetainedSourceFrame :=
  ⟨(retainedFrameEquiv (Classical.choice (inferInstance : Nonempty MaskRetainedTape))).1⟩

private theorem uniform_equiv_weight {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (equivalence : A ≃ B) (weight : A → ℝ≥0∞) :
    (∑' value, (PMF.uniformOfFintype A) value * weight value) =
      ∑' value, (PMF.uniformOfFintype B) value * weight (equivalence.symm value) := by
  have reindex := equivalence.symm.tsum_eq
    (fun value => (PMF.uniformOfFintype A) value * weight value)
  simpa only [PMF.uniformOfFintype_apply, Fintype.card_congr equivalence] using reindex.symm

private theorem uniform_pair_weight {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (weight : A × B → ℝ≥0∞) :
    (∑' pair, (PMF.uniformOfFintype (A × B)) pair * weight pair) =
      ∑' first, (PMF.uniformOfFintype A) first *
        ∑' second, (PMF.uniformOfFintype B) second * weight (first, second) := by
  rw [ENNReal.tsum_prod']
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [← ENNReal.tsum_mul_left, mul_assoc]

/-- The normalized retained tape samples its frame before the independent key and mask. -/
theorem retainedFrame_weight_sum [FieldCertificate] [GroupCertificate]
    [Fintype MaskRetainedTape] [Fintype RetainedSourceFrame] [Fintype BaseField]
    (weight : MaskRetainedTape → ℝ≥0∞) :
    (∑' retained, (PMF.uniformOfFintype MaskRetainedTape) retained * weight retained) =
      ∑' frame : RetainedSourceFrame, (PMF.uniformOfFintype RetainedSourceFrame) frame *
        ∑' key : BaseField, (PMF.uniformOfFintype BaseField) key *
          ∑' mask : NonZeroBase, (PMF.uniformOfFintype NonZeroBase) mask *
            weight (retainedFrameEquiv.symm (frame, key, mask)) := by
  rw [uniform_equiv_weight retainedFrameEquiv,
    uniform_pair_weight (A := RetainedSourceFrame) (B := BaseField × NonZeroBase)]
  apply tsum_congr
  intro frame
  apply congrArg ((PMF.uniformOfFintype RetainedSourceFrame) frame * ·)
  exact uniform_pair_weight (A := BaseField) (B := NonZeroBase) _

/-- The reconstructed frame keeps all row and oracle fields during the key update. -/
theorem retainedFrame_update [FieldCertificate] [GroupCertificate]
    (frame : RetainedSourceFrame) (oldKey key : BaseField) (oldMask mask : NonZeroBase) :
    retainedKeyMask (retainedFrameEquiv.symm (frame, oldKey, oldMask)) key mask =
      retainedFrameEquiv.symm (frame, key, mask) := rfl

end
end Kriterion.ArgoMAC.Security
