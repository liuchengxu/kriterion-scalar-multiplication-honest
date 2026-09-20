import Proof.Privacy.Distribution.SharedOutputEquiv

namespace Kriterion.ArgoMAC.Security
open BN254 FieldMacToECMac Cryptography
noncomputable section
attribute [local instance] Classical.propDecidable vectorFintype rowRandomnessFintype
  xRandomnessFintype yRandomnessFintype zRandomnessFintype

/-- Adaptive scale normalization preserves the actual shared tape law. -/
theorem sharedAdaptiveOutput_normalize [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField) (witness : Shared.Randomness)
    (parameter : Nat) (choose : OutputRowRest → PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → Option Result → OutputRowRest → PMF Observation) :
    (uniformRandomTape Shared.Randomness witness parameter).bind (fun randomness =>
      (choose (actualOutputRest randomness.val)).bind (fun selected =>
        observe selected (actualSelectedOutput scalar selected.1 randomness.val) (actualOutputRest randomness.val))) =
    (uniformRandomTape Shared.Randomness witness parameter).bind (fun randomness =>
      (choose (actualOutputRest randomness.val)).bind (fun selected =>
        observe selected (fullSelectedOutput scalar selected.1
          (nonzeroPointTapeEmbed construction (garblingRandomnessPointEquiv construction randomness.val)))
          (actualOutputRest randomness.val))) := by
  letI : Nonempty Shared.Randomness := ⟨witness⟩
  have same := uniform_bind_viewEquiv_observe
    (fun selected : AffineInput × Aux => sharedSelectedOutputNormalization scalar selected.1)
    (fun randomness => actualOutputRest randomness.val) (fun randomness => actualOutputRest randomness.val)
    (fun selected randomness => selectedOutputNormalization_rest scalar selected.1 randomness.val) choose
    (fun selected randomness => observe selected (fullSelectedOutput scalar selected.1
      (nonzeroPointTapeEmbed construction (garblingRandomnessPointEquiv construction randomness.val)))
      (actualOutputRest randomness.val))
  simpa only [sharedSelectedOutputNormalization, Equiv.subtypeEquiv_apply,
    ← actualSelectedOutput_normalize, selectedOutputNormalization_rest,
    uniformRandomTape, uniformTape_eq] using same

/-- The shared row-source equivalence preserves the view that controls the adaptive choice. -/
theorem sharedOutputRowSourceEquiv_rest [FieldCertificate]
    (source : OffsetRandomness × SharedOffsetRest) :
    (sharedOutputRowSourceEquiv source).val.2.2 = outputRowRest source.2.val := rfl

/-- Adaptive point reindexing keeps the shared oracle and gives the exact target rows. -/
theorem sharedAdaptiveOutput_reindex [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux Observation : Type*} (scalar : ScalarField)
    (choose : OutputRowRest → PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → Option Result → OutputRowRest → PMF Observation) :
    (PMF.uniformOfFintype (OffsetRandomness × SharedOffsetRest)).bind (fun source =>
      (choose (outputRowRest source.2.val)).bind (fun selected =>
        observe selected (fullSelectedOutput scalar selected.1 (source.1, source.2.val))
          (outputRowRest source.2.val))) =
    (PMF.uniformOfFintype SharedOutputRowSource).bind (fun source =>
      (choose source.val.2.2).bind (fun selected =>
        observe selected (idealSelectedOutput scalar selected.1 source.val) source.val.2.2)) := by
  have same := uniform_bind_viewEquiv_observe
    (fun selected : AffineInput × Aux =>
      (sharedSelectedOutputReindex scalar selected.1).trans sharedOutputRowSourceEquiv)
    (fun source => outputRowRest source.2.val) (fun source => source.val.2.2)
    (fun selected source => by
      simp only [Equiv.trans_apply, sharedOutputRowSourceEquiv_rest, sharedSelectedOutputReindex_rest])
    choose (fun selected source =>
      observe selected (idealSelectedOutput scalar selected.1 source.val) source.val.2.2)
  have output (input : AffineInput) (source : OffsetRandomness × SharedOffsetRest) :
      idealSelectedOutput scalar input
        (sharedOutputRowSourceEquiv (sharedSelectedOutputReindex scalar input source)).val =
      fullSelectedOutput scalar input (source.1, source.2.val) := by
    change idealSelectedOutput scalar input (outputRowSourceEquiv
      ((sharedSelectedOutputReindex scalar input source).1,
        (sharedSelectedOutputReindex scalar input source).2.val)) = _
    rw [sharedSelectedOutputReindex_value]
    exact (fullSelectedOutput_reindex scalar input (source.1, source.2.val)).symm
  simpa only [Equiv.trans_apply, output, sharedOutputRowSourceEquiv_rest,
    sharedSelectedOutputReindex_rest] using same

/-- The valid adaptive row law retains the actual shared oracle and costs at most 2^-240. -/
theorem sharedAdaptiveOutput_observation_bound [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (witness : Shared.Randomness) (parameter : Nat)
    (choose : OutputRowRest → PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → Option Result → OutputRowRest → PMF Observation)
    (event : Set Observation) :
    |(((PMF.uniformOfFintype SharedOutputRowSource).bind (fun source =>
        (choose source.val.2.2).bind (fun selected =>
          observe selected (idealSelectedOutput scalar selected.1 source.val) source.val.2.2))).toOuterMeasure event).toReal -
      (((uniformRandomTape Shared.Randomness witness parameter).bind (fun randomness =>
        (choose (actualOutputRest randomness.val)).bind (fun selected =>
          observe selected (actualSelectedOutput scalar selected.1 randomness.val)
            (actualOutputRest randomness.val)))).toOuterMeasure event).toReal| ≤ (2 : ℝ) ^ (-240 : ℤ) := by
  rw [← sharedAdaptiveOutput_reindex scalar choose observe,
    sharedAdaptiveOutput_normalize scalar witness parameter choose observe]
  exact sharedRandomTape_point_observation_bound construction witness parameter
    (fun source => (choose (outputRowRest source.2.val)).bind fun selected =>
      observe selected (fullSelectedOutput scalar selected.1 (source.1, source.2.val))
        (outputRowRest source.2.val)) event

end
end Kriterion.ArgoMAC.Security
