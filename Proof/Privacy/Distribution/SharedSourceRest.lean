import Proof.Privacy.Distribution.SharedOutputEncodingSource
import Proof.Privacy.Distribution.SharedMaskSourceDistribution
import Proof.Privacy.Simulator.SimulatorSourceDistribution

namespace Kriterion.ArgoMAC.Security
open BN254 FieldMacToECMac Cryptography
noncomputable section
attribute [local instance] Classical.propDecidable vectorFintype rowRandomnessFintype
  xRandomnessFintype yRandomnessFintype zRandomnessFintype

/-- The source rest retains the exact shared fixed oracle. -/
abbrev SharedSourceOracleRest := {rest : SourceOracleRest //
  Shared.expandOracle (Shared.restrictOracle rest.2.fixedKeyOracle) = rest.2.fixedKeyOracle}

/-- The retained mask tape separates the oracle rest from its unused row coins. -/
def sharedMaskOracleRestEquiv [FieldCertificate] [GroupCertificate] :
    SharedMaskRetainedTape ≃ SharedSourceOracleRest ×
      (ClampedAffineOffsets × (Fin outputMacCount → NonZeroBase)) where
  toFun tape := (⟨tape.val.2.2, tape.property⟩, tape.val.1, tape.val.2.1)
  invFun source := ⟨(source.2.1, source.2.2, source.1.val), source.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance sharedSourceOracleRestNonempty [FieldCertificate] [GroupCertificate] : Nonempty SharedSourceOracleRest :=
  Nonempty.map (fun tape : SharedMaskRetainedTape => (sharedMaskOracleRestEquiv tape).1) inferInstance

/-- The output rest separates the same shared oracle rest. -/
def sharedOutputOracleRestEquiv : SharedOutputRowRest ≃
    SharedSourceOracleRest ×
      ((Fin outputMacCount → Biquadratic.XRandomness × Biquadratic.YRandomness × Biquadratic.ZRandomness) ×
        (BaseField × BaseField)) where
  toFun rest := (⟨outputSourceOracleRest rest.val, rest.property⟩,
    rest.val.1, rest.val.2.1.curveR1, rest.val.2.1.curveR2)
  invFun source := ⟨(source.2.1,
    ⟨source.1.val.1.1, source.1.val.1.2, source.2.2.1, source.2.2.2⟩,
    source.1.val.2), source.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The retained mask tape has the uniform shared oracle-rest marginal. -/
theorem map_uniform_sharedMaskOracleRest [FieldCertificate] [GroupCertificate] :
    (PMF.uniformOfFintype SharedMaskRetainedTape).map
      (fun tape => (sharedMaskOracleRestEquiv tape).1) = PMF.uniformOfFintype SharedSourceOracleRest := by
  change (PMF.uniformOfFintype SharedMaskRetainedTape).map (Prod.fst ∘ sharedMaskOracleRestEquiv) = _
  rw [← PMF.map_comp, map_uniformOfFintype_equivBetween, map_uniform_prod_fst]

/-- The output rest has the same uniform shared oracle-rest marginal. -/
theorem map_uniform_sharedOutputOracleRest [FieldCertificate] [GroupCertificate] :
    (PMF.uniformOfFintype SharedOutputRowRest).map
      (fun rest => (sharedOutputOracleRestEquiv rest).1) = PMF.uniformOfFintype SharedSourceOracleRest := by
  change (PMF.uniformOfFintype SharedOutputRowRest).map (Prod.fst ∘ sharedOutputOracleRestEquiv) = _
  rw [← PMF.map_comp, map_uniformOfFintype_equivBetween, map_uniform_prod_fst]

/-- The output projection keeps the original source rest. -/
theorem sharedOutputOracleRestEquiv_fst (rest : SharedOutputRowRest) :
    (sharedOutputOracleRestEquiv rest).1.val = outputSourceOracleRest rest.val := rfl

/-- The mask projection keeps the original source rest. -/
theorem sharedMaskOracleRestEquiv_fst [FieldCertificate] [GroupCertificate]
    (tape : SharedMaskRetainedTape) :
    (sharedMaskOracleRestEquiv tape).1.val = tape.val.2.2 := rfl

/-- Both retained tapes give the same observation law for the actual shared oracle rest. -/
theorem sharedOutputMaskRest_observation_eq [FieldCertificate] [GroupCertificate] {Observation : Type*}
    (observe : SourceOracleRest → PMF Observation) :
    (PMF.uniformOfFintype SharedOutputRowRest).bind (fun rest => observe (outputSourceOracleRest rest.val)) =
      (PMF.uniformOfFintype SharedMaskRetainedTape).bind (fun tape => observe tape.val.2.2) := by
  have law := congrArg (fun distribution : PMF SharedSourceOracleRest =>
    distribution.bind (fun rest => observe rest.val))
    (map_uniform_sharedOutputOracleRest.trans map_uniform_sharedMaskOracleRest.symm)
  simpa only [PMF.bind_map, Function.comp_def, sharedOutputOracleRestEquiv_fst,
    sharedMaskOracleRestEquiv_fst] using law

end
end Kriterion.ArgoMAC.Security
