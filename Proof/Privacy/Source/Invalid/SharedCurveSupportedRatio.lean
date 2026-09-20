import Proof.Privacy.Source.Invalid.SharedCurveFullSourceMass
import Proof.Privacy.Source.SharedGateSourceReference
import Proof.Privacy.Source.SharedGateSourceLength

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
set_option maxRecDepth 4096
attribute [local instance 10] Classical.propDecidable
attribute [local instance] bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance curveSupportedKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveSupportedKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
attribute [local irreducible] PMF.uniformOfFintype circuitMaskSampleGarble retainedFullTable
  sharedGateSourceChoose sharedGateSourceObserve

/-- A nonzero curve weight supplies all reference data for its endpoint comparison. -/
theorem sharedCurvePhaseWeight_references [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) (tag : FullCircuitSource)
    (output : SharedFullGateTranscript adversary.State)
    (nonzero : sharedCurveSourcePhaseWeight adversary parameter auxiliary rest keys sample tag output ≠ 0) :
    ∃ first last : Shared.Simulator.OracleState,
      output.2.2.2.1.input = BitInput.ofAffine output.2.1.1 ∧
      sample.2.encodeAffine output.2.1.1 = output.2.2.2.1.inputMac ∧
      OracleTranscriptCompatible idealOracleHandler first output.2.2.1 ∧
      OracleTranscriptCompatible idealOracleHandler last output.2.2.2.2.2 ∧
      PermutationTranscriptMatches first.encOracle
        (encOracleTranscriptRecords (sharedLegacyTranscript (output.2.2.1 ++ output.2.2.2.2.2))) := by
  unfold sharedCurveSourcePhaseWeight at nonzero
  dsimp only at nonzero
  split at nonzero
  next good =>
    have facts := sharedGateSourcePhases_references adversary parameter auxiliary
      (retainedFullTable rest keys tag)
      ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩
      (fun input => selectedGateView (circuitMaskSampleGarble rest.algebraic.field.bridgeKey
        rest.algebraic.field.curveMask.value
        (FieldMacToECMac.rowsForOutputKeys keys rest.algebraic.point.pointRandomness)
        input (retainedFullSource rest tag)) input) output nonzero
    obtain ⟨last, compatible⟩ := facts.2.2.2.1
    exact ⟨_, last, facts.1, facts.2.1, facts.2.2.1, compatible, facts.2.2.2.2⟩
  next bad => exact False.elim (nonzero rfl)

private theorem nonzeroTerm {Index : Type*} (weight : Index → ENNReal)
    (nonzero : (∑' index, weight index) ≠ 0) : ∃ index, weight index ≠ 0 := by
  by_contra missing
  push Not at missing
  exact nonzero (ENNReal.tsum_eq_zero.mpr missing)

/-- Every invalid output satisfies the curve comparison without external reference premises. -/
theorem sharedFullCurveGood_real_le_supported [FieldCertificate] [GroupCertificate] [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) (output : SharedFullGateTranscript adversary.State)
    (invalid : ¬ OnCurve output.2.1.1)
    (budget : Nat) (small : budget ≤ 2 ^ 101)
    (lengthBound : (output.2.2.1 ++ output.2.2.2.2.2).length ≤ budget) :
    (1 - ((54691280 + 368 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128) *
      sourceGoodMass (sharedFullGateTranscriptSamples adversary parameter auxiliary scalar.value witness fallback)
        (fun coin => PMF.pure coin.2.2) {coin | sharedFullCurveBad scalar.value coin} output ≤
      (realAdaptiveTranscriptWithState sharedInternalCircuit
        (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary) output := by
  by_cases zero : sourceGoodMass
      (sharedFullGateTranscriptSamples adversary parameter auxiliary scalar.value witness fallback)
      (fun coin => PMF.pure coin.2.2) {coin | sharedFullCurveBad scalar.value coin} output = 0
  · simp only [zero, mul_zero, zero_le]
  have sumNonzero := zero
  rw [sharedFullCurveGood_weight_sum] at sumNonzero
  obtain ⟨rest, restNonzero⟩ := nonzeroTerm _ sumNonzero
  obtain ⟨tag, tagNonzero⟩ := nonzeroTerm _ ((mul_ne_zero_iff.mp restNonzero).2)
  obtain ⟨sample, sampleNonzero⟩ := nonzeroTerm _ ((mul_ne_zero_iff.mp tagNonzero).2)
  obtain ⟨first, last, bits, mac, firstCompatible, lastCompatible, enc⟩ :=
    sharedCurvePhaseWeight_references adversary parameter auxiliary rest _ sample tag output
      ((mul_ne_zero_iff.mp sampleNonzero).2)
  exact sharedFullCurveGood_real_le adversary parameter auxiliary scalar witness fallback output.1 first last
    output.2.1 output.2.2.2.1 output.2.2.2.2.1 output.2.2.1 output.2.2.2.2.2 sample.2 invalid bits mac
    firstCompatible lastCompatible enc budget small lengthBound

/-- Every supported retained curve weight obeys both adaptive query budgets. -/
theorem sharedCurvePhaseWeight_length_le [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) (tag : FullCircuitSource)
    (output : SharedFullGateTranscript adversary.State)
    (nonzero : sharedCurveSourcePhaseWeight adversary parameter auxiliary rest keys sample tag output ≠ 0) :
    (output.2.2.1 ++ output.2.2.2.2.2).length ≤
      adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter := by
  unfold sharedCurveSourcePhaseWeight at nonzero
  dsimp only at nonzero
  split at nonzero
  next good =>
    exact sharedGateSourcePhases_length_le adversary parameter auxiliary
      (retainedFullTable rest keys tag)
      ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩
      (fun input => selectedGateView (circuitMaskSampleGarble rest.algebraic.field.bridgeKey
        rest.algebraic.field.curveMask.value
        (FieldMacToECMac.rowsForOutputKeys keys rest.algebraic.point.pointRandomness)
        input (retainedFullSource rest tag)) input) output nonzero
  next bad => exact False.elim (nonzero rfl)

/-- The invalid endpoint comparison uses only the advertised adversary query budget. -/
theorem sharedFullCurveGood_real_le_budget [FieldCertificate] [GroupCertificate] [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) (output : SharedFullGateTranscript adversary.State)
    (invalid : ¬ OnCurve output.2.1.1)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter ≤ 2 ^ 101) :
    (1 - ((54691280 + 368 * (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) : Nat) : ENNReal) /
      (2 : ENNReal) ^ 128) *
      sourceGoodMass (sharedFullGateTranscriptSamples adversary parameter auxiliary scalar.value witness fallback)
        (fun coin => PMF.pure coin.2.2) {coin | sharedFullCurveBad scalar.value coin} output ≤
      (realAdaptiveTranscriptWithState sharedInternalCircuit
        (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary) output := by
  by_cases zero : sourceGoodMass
      (sharedFullGateTranscriptSamples adversary parameter auxiliary scalar.value witness fallback)
      (fun coin => PMF.pure coin.2.2) {coin | sharedFullCurveBad scalar.value coin} output = 0
  · simp only [zero, mul_zero, zero_le]
  have sumNonzero := zero
  rw [sharedFullCurveGood_weight_sum] at sumNonzero
  obtain ⟨rest, restNonzero⟩ := nonzeroTerm _ sumNonzero
  obtain ⟨tag, tagNonzero⟩ := nonzeroTerm _ ((mul_ne_zero_iff.mp restNonzero).2)
  obtain ⟨sample, sampleNonzero⟩ := nonzeroTerm _ ((mul_ne_zero_iff.mp tagNonzero).2)
  exact sharedFullCurveGood_real_le_supported adversary parameter auxiliary scalar witness fallback output invalid _ small
    (sharedCurvePhaseWeight_length_le adversary parameter auxiliary rest _ sample tag output
      ((mul_ne_zero_iff.mp sampleNonzero).2))

end
end Kriterion.ArgoMAC.Security
