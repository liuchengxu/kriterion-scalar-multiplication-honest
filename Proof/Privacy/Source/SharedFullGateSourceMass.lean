import Proof.Privacy.Source.SharedGateSourceEntrance
import Proof.Privacy.Source.PrefixGoodExpansion

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1
  instFintypeCircuitMaskTables instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

/-- The prefix source retains the actual shared tape and the complete hash tag. -/
def sharedFullGatePrefixSamples [FieldCertificate] [GroupCertificate] {Prefix : Type*}
    (scalar : ScalarField) (witness : Shared.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Prefix)) :=
  (uniformRandomTape Shared.Randomness witness parameter).bind fun randomness =>
    (PMF.uniformOfFintype FullCircuitSource).bind fun tag =>
      let retained := maskRetainedTape randomness.val
      let source := decodeFullSource (tag.1, sharedCircuitHashRest randomness.val tag.2)
      let table := circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
        (retainedSourceRows scalar retained) source
      (choose table retained.2.2).map fun selected => (randomness, tag, selected)

/-- The shared prefix kernel uses the exact deterministic full-source continuation. -/
def sharedFullGatePrefixKernel [FieldCertificate] [GroupCertificate] {Prefix Observation : Type*}
    (scalar : ScalarField)
    (observe : Pipeline.Table → (AffineInput × Prefix) → SelectedGateView →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (sample : Shared.Randomness × FullCircuitSource × (AffineInput × Prefix)) : PMF Observation :=
  fullGatePrefixKernel scalar observe fallback (sample.1.val, sample.2)

/-- The shared prefix source has the exact full-source observation law. -/
theorem sharedFullGatePrefixSamples_bind [FieldCertificate] [GroupCertificate] {Prefix Observation : Type*}
    (scalar : ScalarField) (witness : Shared.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Prefix))
    (observe : Pipeline.Table → (AffineInput × Prefix) → SelectedGateView →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation) :
    (sharedFullGatePrefixSamples scalar witness parameter choose).bind
      (sharedFullGatePrefixKernel scalar observe fallback) =
        actualSharedFullGateSource scalar witness parameter choose observe fallback := by
  simp only [sharedFullGatePrefixSamples, actualSharedFullGateSource,
    PMF.bind_bind, PMF.bind_map, Function.comp_def]
  apply congrArg (uniformRandomTape Shared.Randomness witness parameter).bind
  funext randomness
  apply congrArg₂ PMF.bind
  · apply congrArg (fun finite => @PMF.uniformOfFintype FullCircuitSource finite inferInstance)
    exact Subsingleton.elim _ _
  funext tag
  by_cases complete : FullSourceComplete tag.1
  · simp only [sharedFullGatePrefixKernel, fullGatePrefixKernel, fullGateSourceRun,
      complete, if_true, retainedGateSourceRun]
  · simp only [sharedFullGatePrefixKernel, fullGatePrefixKernel, fullGateSourceRun,
      complete, if_false, PMF.bind_const]

/-- The good prefix mass keeps every shared tape and full tag in its exact sum. -/
theorem sharedFullGatePrefixGood_mass [FieldCertificate] [GroupCertificate] {Prefix Observation : Type*}
    (scalar : ScalarField) (witness : Shared.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Prefix))
    (kernel : (Shared.Randomness × FullCircuitSource × (AffineInput × Prefix)) → PMF Observation)
    (bad : Set (Shared.Randomness × FullCircuitSource × (AffineInput × Prefix))) (output : Observation) :
    sourceGoodMass (sharedFullGatePrefixSamples scalar witness parameter choose) kernel bad output =
      ∑' randomness, (uniformRandomTape Shared.Randomness witness parameter) randomness *
        ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
          sourceGoodMass (choose
            (circuitMaskSourceTable (maskRetainedTape randomness.val).2.2.1.1
              (maskRetainedTape randomness.val).2.2.1.2.value
              (retainedSourceRows scalar (maskRetainedTape randomness.val))
              (decodeFullSource (tag.1, sharedCircuitHashRest randomness.val tag.2)))
            (maskRetainedTape randomness.val).2.2)
            (fun selected => kernel (randomness, tag, selected))
            {selected | bad (randomness, tag, selected)} output := by
  exact sourceGoodMass_nested_map (uniformRandomTape Shared.Randomness witness parameter)
    (PMF.uniformOfFintype FullCircuitSource) _ _ kernel bad output _ rfl

end
end Kriterion.ArgoMAC.Security
