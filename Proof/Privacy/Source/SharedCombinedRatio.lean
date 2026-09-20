import Proof.Privacy.Source.SharedCombinedSource

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
set_option maxRecDepth 4096
attribute [local instance 10] Classical.propDecidable
attribute [local irreducible] PMF.uniformOfFintype circuitMaskSampleGarble sharedGateSourceChoose sharedGateSourceObserve

/-- Every good shared prefix continuation obeys the actual adversary query budget. -/
theorem sharedFullPipelineGood_length_le [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) (output : SharedFullGateTranscript adversary.State)
    (nonzero : sourceGoodMass (sharedFullGatePrefixSamples scalar witness parameter
      (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2))
      (sharedFullGatePrefixKernel scalar
        (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback) {coin | sharedFullPipelinePrefixBad scalar coin} output ≠ 0) :
    (output.2.2.1 ++ output.2.2.2.2.2).length ≤
      adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter := by
  obtain ⟨coin, coinMember, good, outputMember⟩ := sourceGoodMass_support _ _ _ _ nonzero
  have complete := (Classical.not_not.mp good).1
  simp only [sharedFullGatePrefixSamples, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at coinMember
  obtain ⟨randomness, _, tag, _, selected, selectedMember, same⟩ := coinMember
  cases same
  simp only [sharedFullGatePrefixKernel, fullGatePrefixKernel, complete, if_true] at outputMember
  exact sharedGateSourcePhases_length_le adversary parameter auxiliary _ _ _ output
    ((PMF.mem_support_bind_iff _ _ _).mpr ⟨selected, selectedMember, outputMember⟩)

/-- The larger curve loss also covers the complete pipeline relative loss. -/
theorem sharedCombinedFactor_le_pipeline (budget : Nat) :
    1 - ((54691280 + 368 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128 ≤
      1 - ((54690772 + 364 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128 := by
  apply tsub_le_tsub_left
  apply ENNReal.div_le_div_right
  exact_mod_cast (show 54690772 + 364 * budget ≤ 54691280 + 368 * budget by omega)

/-- One complete shared source guard gives the same real endpoint ratio for both input branches. -/
theorem sharedCombinedGood_real_le [FieldCertificate] [GroupCertificate] [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) (output : SharedFullGateTranscript adversary.State)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter ≤ 2 ^ 101) :
    (1 - ((54691280 + 368 * (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) : Nat) : ENNReal) /
      (2 : ENNReal) ^ 128) *
      sourceGoodMass (sharedCombinedSource adversary parameter auxiliary scalar.value witness fallback)
        (fun coin => PMF.pure coin.2) {coin | sharedCombinedBad scalar.value coin} output ≤
      (realAdaptiveTranscriptWithState sharedInternalCircuit
        (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary) output := by
  by_cases valid : OnCurve output.2.1.1
  · have comparison := sharedCombinedGood_prefix_le adversary parameter auxiliary scalar.value witness fallback output
    by_cases zero : sourceGoodMass (sharedFullGatePrefixSamples scalar.value witness parameter
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2))
        (sharedFullGatePrefixKernel scalar.value
          (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
          fallback) {coin | sharedFullPipelinePrefixBad scalar.value coin} output = 0
    · have combinedZero := le_antisymm (comparison.trans_eq zero) bot_le
      simp only [combinedZero, mul_zero, zero_le]
    · exact (mul_le_mul' (sharedCombinedFactor_le_pipeline _) comparison).trans
        (sharedFullPipelinePrefix_real_le_supported adversary parameter auxiliary scalar witness fallback output valid _ small
          (sharedFullPipelineGood_length_le adversary parameter auxiliary scalar.value witness fallback output zero))
  · exact (mul_le_mul_right
      (sharedCombinedGood_curve_le adversary parameter auxiliary scalar.value witness fallback output valid) _).trans
      (sharedFullCurveGood_real_le_budget adversary parameter auxiliary scalar witness fallback output valid small)

end
end Kriterion.ArgoMAC.Security
