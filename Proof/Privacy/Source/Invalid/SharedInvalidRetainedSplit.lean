import Proof.Privacy.Distribution.SharedMaskSourceDistribution

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
noncomputable section
attribute [local instance 10] Classical.propDecidable
attribute [local instance] vectorFintype rowRandomnessFintype xRandomnessFintype yRandomnessFintype zRandomnessFintype

/-- This source fixes the rows and shared oracle data before either curve field coin. -/
abbrev SharedCurveFixedSource [FieldCertificate] [GroupCertificate] :=
  {source : ClampedAffineOffsets × (Fin outputMacCount → NonZeroBase) × GarblingOracleData //
    Shared.expandOracle (Shared.restrictOracle source.2.2.fixedKeyOracle) = source.2.2.fixedKeyOracle}

/-- The actual retained tape has independent bridge and nonzero-mask coins. -/
def sharedCurveFixedSourceEquiv [FieldCertificate] [GroupCertificate] :
    SharedMaskRetainedTape ≃ SharedCurveFixedSource × (BaseField × NonZeroBase) where
  toFun tape := (⟨(tape.val.1, tape.val.2.1, tape.val.2.2.2), tape.property⟩, tape.val.2.2.1)
  invFun source := ⟨(source.1.val.1, source.1.val.2.1, source.2, source.1.val.2.2), source.1.property⟩
  left_inv tape := by cases tape; rfl
  right_inv source := by cases source; rfl

local instance fixedCurveSourceNonempty [FieldCertificate] [GroupCertificate] : Nonempty SharedCurveFixedSource :=
  ⟨(sharedCurveFixedSourceEquiv (Classical.choice (inferInstance : Nonempty SharedMaskRetainedTape))).1⟩

/-- The exact retained average samples the fixed source before the two independent field coins. -/
theorem sharedCurveFixedSource_observation [FieldCertificate] [GroupCertificate] {Observation : Type*}
    (observe : SharedMaskRetainedTape → PMF Observation) :
    (PMF.uniformOfFintype SharedMaskRetainedTape).bind observe =
      (PMF.uniformOfFintype SharedCurveFixedSource).bind fun source =>
        (PMF.uniformOfFintype BaseField).bind fun bridge =>
          (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
            observe (sharedCurveFixedSourceEquiv.symm (source, bridge, mask)) := by
  have law := congrArg (fun distribution => distribution.bind
    (fun source => observe (sharedCurveFixedSourceEquiv.symm source)))
    (map_uniformOfFintype_equivBetween sharedCurveFixedSourceEquiv)
  simp only [PMF.bind_map, Function.comp_def, Equiv.symm_apply_apply] at law
  rw [law, uniform_product_bind]
  apply congrArg (PMF.uniformOfFintype SharedCurveFixedSource).bind
  funext source
  rw [uniform_product_bind]

end
end Kriterion.ArgoMAC.Security
