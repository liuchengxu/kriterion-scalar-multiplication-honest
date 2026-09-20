import Proof.Privacy.Source.Valid.SharedPipelinePhaseSum
import Proof.Privacy.Source.SharedRetainedTableAlignment
import Proof.Privacy.Source.SharedFullGateSourceMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance pipelinePrefixKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance pipelinePrefixKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
attribute [local irreducible] circuitMaskSampleGarble retainedFullTable PMF.uniformOfFintype
  sharedGateSourceChoose sharedGateSourceObserve
set_option maxRecDepth 2048

/-- The actual shared prefix guard checks complete tags, point rows, and the fresh selected schedule. -/
def sharedFullPipelinePrefixBad [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField)
    (sample : Shared.Randomness × FullCircuitSource ×
      (AffineInput × (State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))) : Prop :=
  let rest := (sharedGarblingOracleKeyEquiv sample.1).2
  let keys := outputKeys construction scalar rest.reference.offsets
  ¬ SharedPipelineTagGood rest keys (retainedFullTable rest keys sample.2.1) sample.2.2.1
    sample.1.val.inputMacKey
    (transcriptFinalState idealOracleHandler
      (sharedInitialSourceOracle (maskRetainedTape sample.1.val).2.2.2) sample.2.2.2.2.2) sample.2.1

/-- The restored shared prefix guard is the exact retained pipeline guard. -/
theorem sharedFullPipelinePrefixBad_oracleKey [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField) (rest : GarblingSourceRest)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) (tag : FullCircuitSource)
    (selected : AffineInput × (State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer))) :
    sharedFullPipelinePrefixBad scalar (sharedGarblingOracleKeyEquiv.symm (sample, rest), tag, selected) ↔
      ¬ SharedPipelineTagGood rest (outputKeys construction scalar rest.reference.offsets)
        (retainedFullTable rest (outputKeys construction scalar rest.reference.offsets) tag) selected.1 sample.2
        (transcriptFinalState idealOracleHandler
          (sharedInitialSourceOracle ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩)
          selected.2.2.2) tag := by
  simp only [sharedFullPipelinePrefixBad, Equiv.apply_symm_apply, maskRetainedTape_sharedOracleKey_data]
  rfl

/-- The actual shared prefix component has the exact retained phase weight. -/
theorem sharedFullPipelinePrefix_component [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (rest : GarblingSourceRest) (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)
    (tag : FullCircuitSource)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State))
    (output : SharedFullGateTranscript adversary.State) :
    sourceGoodMass
      (sharedGateSourceChoose adversary parameter auxiliary
        (circuitMaskSourceTable
          (maskRetainedTape (sharedGarblingOracleKeyEquiv.symm (sample, rest)).val).2.2.1.1
          (maskRetainedTape (sharedGarblingOracleKeyEquiv.symm (sample, rest)).val).2.2.1.2.value
          (retainedSourceRows scalar (maskRetainedTape (sharedGarblingOracleKeyEquiv.symm (sample, rest)).val))
          (decodeFullSource (tag.1, sharedCircuitHashRest (sharedGarblingOracleKeyEquiv.symm (sample, rest)).val tag.2)))
        (maskRetainedTape (sharedGarblingOracleKeyEquiv.symm (sample, rest)).val).2.2.2)
      (fun selected => sharedFullGatePrefixKernel scalar
        (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback (sharedGarblingOracleKeyEquiv.symm (sample, rest), tag, selected))
      {selected | sharedFullPipelinePrefixBad scalar (sharedGarblingOracleKeyEquiv.symm (sample, rest), tag, selected)}
      output = sharedPipelinePhaseWeight adversary parameter auxiliary rest
        (outputKeys construction scalar rest.reference.offsets) sample tag output := by
  rw [← retainedFullTable_sharedPrefixTable scalar rest sample tag, maskRetainedTape_sharedOracleKey_data]
  unfold sharedPipelinePhaseWeight sourceGoodMass
  apply tsum_congr
  intro selected
  simp only [Set.mem_setOf_eq]
  rw [sharedFullPipelinePrefixBad_oracleKey scalar rest sample tag selected]
  by_cases good : SharedPipelineTagGood rest (outputKeys construction scalar rest.reference.offsets)
      (retainedFullTable rest (outputKeys construction scalar rest.reference.offsets) tag) selected.1 sample.2
      (transcriptFinalState idealOracleHandler
        (sharedInitialSourceOracle ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩)
        selected.2.2.2) tag
  · simp only [good, not_true_eq_false, if_false]
    congr 1
    simp only [sharedFullGatePrefixKernel, fullGatePrefixKernel, good.1, if_true,
      retainedSourceRows_sharedOracleKey, sharedCircuitHashRest_sharedOracleKey,
      maskRetainedTape_sharedOracleKey_data]
    unfold retainedFullTable
    rfl
  · simp only [good, not_false_eq_true, if_true]

attribute [local irreducible] sharedPipelinePhaseWeight

/-- The actual good shared prefix mass has the complete retained phase-weight sum. -/
theorem sharedFullPipelinePrefix_weight_sum [FieldCertificate] [GroupCertificate] [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) (output : SharedFullGateTranscript adversary.State) :
    letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
    sourceGoodMass (sharedFullGatePrefixSamples scalar witness parameter
      (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2))
      (sharedFullGatePrefixKernel scalar
        (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback) {sample | sharedFullPipelinePrefixBad scalar sample} output =
      ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
        ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
          ∑' sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey,
            (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)) sample *
              sharedPipelinePhaseWeight adversary parameter auxiliary rest
                (outputKeys construction scalar rest.reference.offsets) sample tag output := by
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  unfold sharedFullGatePrefixSamples
  rw [sharedRandomTape_oracleKey]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, sourceGoodMass_bind, sourceGoodMass_map]
  simp only [Set.preimage_setOf_eq]
  apply tsum_congr
  intro rest
  congr 1
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro tag
  apply tsum_congr
  intro sample
  rw [sharedFullPipelinePrefix_component adversary parameter auxiliary scalar rest sample tag fallback output]
  exact mul_left_comm _ _ _

/-- The good shared pipeline prefix satisfies the exact real endpoint ratio. -/
theorem sharedFullPipelinePrefix_real_le [FieldCertificate] [GroupCertificate] [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State))
    (table : Pipeline.Table) (referenceBefore referenceAfter : Shared.Simulator.OracleState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (key : InputMacKey)
    (valid : OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after)
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : (before ++ after).length ≤ budget) :
    (1 - ((54690772 + 364 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128) *
      sourceGoodMass (sharedFullGatePrefixSamples scalar.value witness parameter
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2))
        (sharedFullGatePrefixKernel scalar.value
          (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
          fallback) {sample | sharedFullPipelinePrefixBad scalar.value sample}
        (table, selected, before, labels, decision, after) ≤
      (realAdaptiveTranscriptWithState sharedInternalCircuit
        (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary)
          (table, selected, before, labels, decision, after) := by
  rw [sharedFullPipelinePrefix_weight_sum]
  rw [show (fun a b : RawCircuitGate => Classical.propDecidable (a = b)) =
    pipelinePhaseSumGateDecidableEq from Subsingleton.elim _ _]
  exact sharedPipelinePhaseWeight_sum_real_le adversary parameter auxiliary scalar witness table
    referenceBefore referenceAfter selected labels decision before after key valid bits mac
    firstCompatible secondCompatible budget small lengthBound

end
end Kriterion.ArgoMAC.Security
