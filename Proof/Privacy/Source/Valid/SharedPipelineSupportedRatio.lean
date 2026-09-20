import Proof.Privacy.Source.Valid.SharedPipelinePrefixMass
import Proof.Privacy.Source.SourceReferenceSupport
import Proof.Privacy.Source.SharedGateSourceReference

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
set_option maxRecDepth 4096
attribute [local instance 10] Classical.propDecidable
attribute [local instance] bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance pipelineSupportedKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance pipelineSupportedKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
attribute [local irreducible] PMF.uniformOfFintype circuitMaskSampleGarble retainedFullTable
  sharedGateSourceChoose sharedGateSourceObserve

/-- A nonzero pipeline weight supplies all reference data for its endpoint comparison. -/
theorem sharedPipelinePhaseWeight_references [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) (tag : FullCircuitSource)
    (output : SharedFullGateTranscript adversary.State)
    (nonzero : sharedPipelinePhaseWeight adversary parameter auxiliary rest keys sample tag output ≠ 0) :
    ∃ first last : Shared.Simulator.OracleState,
      output.2.2.2.1.input = BitInput.ofAffine output.2.1.1 ∧
      sample.2.encodeAffine output.2.1.1 = output.2.2.2.1.inputMac ∧
      OracleTranscriptCompatible idealOracleHandler first output.2.2.1 ∧
      OracleTranscriptCompatible idealOracleHandler last output.2.2.2.2.2 ∧
      PermutationTranscriptMatches first.encOracle
        (encOracleTranscriptRecords (sharedLegacyTranscript (output.2.2.1 ++ output.2.2.2.2.2))) := by
  unfold sharedPipelinePhaseWeight at nonzero
  dsimp only at nonzero
  obtain ⟨selected, firstMember, _, lastMember⟩ := sourceGoodMass_support _ _ _ _ nonzero
  have facts := sharedGateSourcePhases_references adversary parameter auxiliary
    (retainedFullTable rest keys tag)
    ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩
    (fun input => selectedGateView (circuitMaskSampleGarble rest.algebraic.field.bridgeKey
      rest.algebraic.field.curveMask.value
      (FieldMacToECMac.rowsForOutputKeys keys rest.algebraic.point.pointRandomness)
      input (retainedFullSource rest tag)) input) output ((PMF.mem_support_bind_iff _ _ _).mpr ⟨selected, firstMember, lastMember⟩)
  obtain ⟨last, compatible⟩ := facts.2.2.2.1
  exact ⟨_, last, facts.1, facts.2.1, facts.2.2.1, compatible, facts.2.2.2.2⟩

private theorem nonzeroTerm {Index : Type*} (weight : Index → ENNReal)
    (nonzero : (∑' index, weight index) ≠ 0) : ∃ index, weight index ≠ 0 := by
  by_contra missing
  push Not at missing
  exact nonzero (ENNReal.tsum_eq_zero.mpr missing)

/-- Every valid output satisfies the pipeline comparison without external reference premises. -/
theorem sharedFullPipelinePrefix_real_le_supported [FieldCertificate] [GroupCertificate] [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) (output : SharedFullGateTranscript adversary.State)
    (valid : OnCurve output.2.1.1)
    (budget : Nat) (small : budget ≤ 2 ^ 101)
    (lengthBound : (output.2.2.1 ++ output.2.2.2.2.2).length ≤ budget) :
    (1 - ((54690772 + 364 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128) *
      sourceGoodMass (sharedFullGatePrefixSamples scalar.value witness parameter
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2))
        (sharedFullGatePrefixKernel scalar.value
          (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
          fallback) {sample | sharedFullPipelinePrefixBad scalar.value sample} output ≤
      (realAdaptiveTranscriptWithState sharedInternalCircuit
        (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary) output := by
  by_cases zero : sourceGoodMass
      (sharedFullGatePrefixSamples scalar.value witness parameter
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2))
        (sharedFullGatePrefixKernel scalar.value
          (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
          fallback) {sample | sharedFullPipelinePrefixBad scalar.value sample} output = 0
  · simp only [zero, mul_zero, zero_le]
  have sumNonzero := zero
  rw [sharedFullPipelinePrefix_weight_sum] at sumNonzero
  obtain ⟨rest, restNonzero⟩ := nonzeroTerm _ sumNonzero
  obtain ⟨tag, tagNonzero⟩ := nonzeroTerm _ ((mul_ne_zero_iff.mp restNonzero).2)
  obtain ⟨sample, sampleNonzero⟩ := nonzeroTerm _ ((mul_ne_zero_iff.mp tagNonzero).2)
  obtain ⟨first, last, bits, mac, firstCompatible, lastCompatible, enc⟩ :=
    sharedPipelinePhaseWeight_references adversary parameter auxiliary rest _ sample tag output
      ((mul_ne_zero_iff.mp sampleNonzero).2)
  exact sharedFullPipelinePrefix_real_le adversary parameter auxiliary scalar witness fallback output.1 first last
    output.2.1 output.2.2.2.1 output.2.2.2.2.1 output.2.2.1 output.2.2.2.2.2 sample.2 valid bits mac
    firstCompatible lastCompatible budget small lengthBound

end
end Kriterion.ArgoMAC.Security
