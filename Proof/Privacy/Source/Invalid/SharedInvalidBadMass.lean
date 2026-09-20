import Proof.Privacy.Source.Invalid.SharedInvalidFullHashMass
import Proof.Privacy.Source.Invalid.SharedCurveGuardFromPipeline
import Proof.Privacy.Source.SharedFullTranscriptPrefix
import Proof.Privacy.Source.Valid.SharedPipelinePrefixMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
set_option maxRecDepth 4096
attribute [local instance 10] Classical.propDecidable
attribute [local irreducible] PMF.uniformOfFintype circuitMaskSampleGarble retainedFullTable
  circuitMaskSourceTable FreshRecordSchedule sharedRetainedPipelineCommands sharedRetainedCurveCommands

/-- The full invalid guard adds only a complete hidden-bridge hit to the pipeline prefix guard. -/
theorem sharedInvalidCurveBad_kernel [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (coin : Shared.Randomness × FullCircuitSource ×
      (AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer))))
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) (output : SharedFullGateTranscript adversary.State)
    (member : output ∈ (sharedFullGatePrefixKernel scalar
      (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
      fallback coin).support)
    (invalid : ¬ OnCurve output.2.1.1)
    (bad : sharedFullCurveBad scalar (coin.1, coin.2.1, output)) :
    sharedFullPipelinePrefixBad scalar coin ∨ sharedFullInvalidHashHit (coin.1, coin.2.1, output) := by
  by_cases prior : sharedFullPipelinePrefixBad scalar coin
  · exact Or.inl prior
  have good := Classical.not_not.mp prior
  change SharedPipelineTagGood _ _ _ _ _ _ _ at good
  have complete := good.1
  simp only [sharedFullGatePrefixKernel, fullGatePrefixKernel, complete, if_true] at member
  have recorded := sharedGateSourceObserve_tag adversary parameter auxiliary _ _ _ _ output member
  have table := congrArg (fun value => value.1) recorded
  have input := congrArg (fun value => value.2.1.1) recorded
  have history := congrArg (fun value => value.2.2.1) recorded
  dsimp only at table input history
  have pipeline : SharedPipelineTagGood (sharedGarblingOracleKeyEquiv coin.1).2
      (outputKeys construction scalar (sharedGarblingOracleKeyEquiv coin.1).2.reference.offsets)
      output.1 output.2.1.1 coin.1.val.inputMacKey
      (transcriptFinalState idealOracleHandler
        (sharedInitialSourceOracle (maskRetainedTape coin.1.val).2.2.2) output.2.2.1) coin.2.1 := by
    rw [input, history, table]
    have alignment := retainedFullTable_sharedPrefixTable scalar (sharedGarblingOracleKeyEquiv coin.1).2
      (sharedGarblingOracleKeyEquiv coin.1).1 coin.2.1
    rw [Equiv.symm_apply_apply] at alignment
    rw [← alignment]
    exact good
  have failure := sharedCurveTagBad_subset (sharedGarblingOracleKeyEquiv coin.1).2
    (outputKeys construction scalar (sharedGarblingOracleKeyEquiv coin.1).2.reference.offsets)
    output.1 output.2.1.1 coin.1.val.inputMacKey _ _ coin.2.1 bad
  exact Or.inr ⟨complete, invalid, failure.resolve_left (not_not.mpr pipeline)⟩

private theorem projectedBad_le {Source Output Target : Type*}
    (samples : PMF Source) (kernel : Source → PMF Output) (project : Source → Output → Target)
    (bad : Set Target) (prior : Set Source) (extra : Set Target)
    (included : ∀ source ∈ samples.support, ∀ output ∈ (kernel source).support,
      project source output ∈ bad → source ∈ prior ∨ project source output ∈ extra) :
    (samples.bind fun source => (kernel source).map (project source)).toOuterMeasure bad ≤
      samples.toOuterMeasure prior +
        (samples.bind fun source => (kernel source).map (project source)).toOuterMeasure extra := by
  let joint := samples.bind fun source => (kernel source).map (Prod.mk source)
  have projection : joint.map (fun pair => project pair.1 pair.2) =
      samples.bind fun source => (kernel source).map (project source) := by
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have first : joint.map Prod.fst = samples := by
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
    have constant (source : Source) : (kernel source).map (fun _ => source) = PMF.pure source := PMF.map_const _ _
    simp_rw [constant]
    exact PMF.bind_pure samples
  rw [← projection, PMF.toOuterMeasure_map_apply]
  apply le_trans (joint.toOuterMeasure_mono (t := (Prod.fst ⁻¹' prior) ∪
    ((fun pair => project pair.1 pair.2) ⁻¹' extra)) ?_) ?_
  · rintro pair ⟨badPair, supported⟩
    obtain ⟨source, sourceMember, mapped⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
    obtain ⟨output, outputMember, same⟩ := (PMF.mem_support_map_iff _ _ _).mp mapped
    cases same
    exact included source sourceMember output outputMember badPair
  · apply (MeasureTheory.measure_union_le _ _).trans_eq
    rw [← PMF.toOuterMeasure_map_apply, first, ← PMF.toOuterMeasure_map_apply, projection]

/-- The full invalid bad mass is bounded by the pipeline prefix failure and hidden-bridge event. -/
theorem sharedFullInvalidBad_mass_le [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) :
    (sharedFullGateTranscriptSamples adversary parameter auxiliary scalar witness fallback).toOuterMeasure
      {coin | ¬ OnCurve coin.2.2.2.1.1 ∧ sharedFullCurveBad scalar coin} ≤
      (sharedFullGatePrefixSamples scalar witness parameter
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)).toOuterMeasure
        {coin | sharedFullPipelinePrefixBad scalar coin} +
      (sharedFullGateTranscriptSamples adversary parameter auxiliary scalar witness fallback).toOuterMeasure
        {coin | sharedFullInvalidHashHit coin} := by
  rw [sharedFullGateTranscriptSamples_prefix]
  exact projectedBad_le _ _ _ _ _ _ (fun coin _ output member bad =>
    sharedInvalidCurveBad_kernel adversary parameter auxiliary scalar coin fallback output member bad.1 bad.2)

end
end Kriterion.ArgoMAC.Security
