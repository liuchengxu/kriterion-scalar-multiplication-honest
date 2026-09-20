import Proof.Privacy.Source.Invalid.SharedCurvePhaseSum
import Proof.Privacy.Source.SharedRetainedTableAlignment
import Proof.Privacy.Source.SharedFullGateSourceMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
set_option maxRecDepth 4096
attribute [local instance 10] Classical.propDecidable
attribute [local instance] bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance curveFullKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveFullKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
attribute [local irreducible] circuitMaskSampleGarble retainedFullTable PMF.uniformOfFintype

/-- This source keeps the shared tape, complete tag, and complete observed transcript. -/
def sharedFullGateTranscriptSamples [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) :=
  (uniformRandomTape Shared.Randomness witness parameter).bind fun randomness =>
    (PMF.uniformOfFintype FullCircuitSource).bind fun tag =>
      (fullGateSourceRun scalar (maskRetainedTape randomness.val)
        (tag.1, sharedCircuitHashRest randomness.val tag.2)
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
        (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback).map fun output => (randomness, tag, output)

/-- Hiding the retained source gives the exact shared full-source transcript. -/
theorem sharedFullGateTranscriptSamples_project [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) :
    (sharedFullGateTranscriptSamples adversary parameter auxiliary scalar witness fallback).bind
      (fun coin => PMF.pure coin.2.2) =
      actualSharedFullGateSource scalar witness parameter
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
        (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback := by
  simp only [sharedFullGateTranscriptSamples, PMF.bind_bind, PMF.bind_map, Function.comp_def,
    PMF.bind_pure, actualSharedFullGateSource]
  apply congrArg (uniformRandomTape Shared.Randomness witness parameter).bind
  funext randomness
  apply congrArg₂ PMF.bind
  · apply congrArg (fun finite => @PMF.uniformOfFintype FullCircuitSource finite inferInstance)
    exact Subsingleton.elim _ _
  rfl

/-- This full-source event checks the curve guard against both observed phases. -/
def sharedFullCurveBad [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField) (coin : Shared.Randomness × FullCircuitSource × SharedFullGateTranscript State) : Prop :=
  let rest := (sharedGarblingOracleKeyEquiv coin.1).2
  let output := coin.2.2
  ¬ SharedCurveTagGood rest (outputKeys construction scalar rest.reference.offsets)
    output.1 output.2.1.1 coin.1.val.inputMacKey
    (transcriptFinalState idealOracleHandler
      (sharedInitialSourceOracle (maskRetainedTape coin.1.val).2.2.2) output.2.2.1)
    (output.2.2.1 ++ output.2.2.2.2.2) coin.2.1

/-- A retained transcript has its exact guarded point mass. -/
private theorem recordedGoodMass {Transcript Source : Type*} (samples : PMF Transcript)
    (record : Transcript → Source) (project : Source → Transcript)
    (left : ∀ output, project (record output) = output) (bad : Set Source) (output : Transcript) :
    sourceGoodMass (samples.map record) (fun source => PMF.pure (project source)) bad output =
      if record output ∈ bad then 0 else samples output := by
  rw [sourceGoodMass_map, sourceGoodMass, tsum_eq_single output]
  · simp only [left, PMF.pure_apply_self, Set.mem_preimage]
    split <;> simp_all only [mul_zero, mul_one]
  · intro other different
    simp [left, PMF.pure_apply, Ne.symm different]

/-- The full shared source guard gives exactly the retained curve weight. -/
theorem sharedFullCurve_component [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (rest : GarblingSourceRest) (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)
    (tag : FullCircuitSource)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) (output : SharedFullGateTranscript adversary.State) :
    sourceGoodMass
      ((fullGateSourceRun scalar (maskRetainedTape (sharedGarblingOracleKeyEquiv.symm (sample, rest)).val)
        (tag.1, sharedCircuitHashRest (sharedGarblingOracleKeyEquiv.symm (sample, rest)).val tag.2)
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
        (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback).map fun result => (sharedGarblingOracleKeyEquiv.symm (sample, rest), tag, result))
      (fun coin => PMF.pure coin.2.2) {coin | sharedFullCurveBad scalar coin} output =
      sharedCurveSourcePhaseWeight adversary parameter auxiliary rest
        (outputKeys construction scalar rest.reference.offsets) sample tag output := by
  have keyEq : (sharedGarblingOracleKeyEquiv.symm (sample, rest)).val.inputMacKey = sample.2 := rfl
  rw [recordedGoodMass _ _ _ (fun _ => rfl)]
  simp only [Set.mem_setOf_eq, sharedFullCurveBad, Equiv.apply_symm_apply,
    maskRetainedTape_sharedOracleKey_data, keyEq]
  unfold sharedCurveSourcePhaseWeight
  dsimp only
  split_ifs with good
  · simp only [fullGateSourceRun, good.1, if_true, retainedGateSourceRun,
      retainedSourceRows_sharedOracleKey, sharedCircuitHashRest_sharedOracleKey,
      maskRetainedTape_sharedOracleKey_data]
    unfold retainedFullTable
    rfl
  · rfl

attribute [local irreducible] sharedCurveSourcePhaseWeight

/-- The full shared good-source mass has the exact retained curve sum. -/
theorem sharedFullCurveGood_weight_sum [FieldCertificate] [GroupCertificate] [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) (output : SharedFullGateTranscript adversary.State) :
    letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
    sourceGoodMass (sharedFullGateTranscriptSamples adversary parameter auxiliary scalar witness fallback)
      (fun coin => PMF.pure coin.2.2) {coin | sharedFullCurveBad scalar coin} output =
      ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
        ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
          ∑' sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey,
            (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)) sample *
              sharedCurveSourcePhaseWeight adversary parameter auxiliary rest
                (outputKeys construction scalar rest.reference.offsets) sample tag output := by
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  unfold sharedFullGateTranscriptSamples
  rw [sharedRandomTape_oracleKey]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, sourceGoodMass_bind]
  apply tsum_congr
  intro rest
  congr 1
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro tag
  apply tsum_congr
  intro sample
  rw [sharedFullCurve_component]
  ac_rfl

/-- The full good shared curve source satisfies the exact real endpoint ratio. -/
theorem sharedFullCurveGood_real_le [FieldCertificate] [GroupCertificate] [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State))
    (table : Pipeline.Table) (referenceBefore referenceAfter : Shared.Simulator.OracleState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (key : InputMacKey)
    (invalid : ¬ OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after)
    (encReference : PermutationTranscriptMatches referenceBefore.encOracle
      (encOracleTranscriptRecords (sharedLegacyTranscript (before ++ after))))
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : (before ++ after).length ≤ budget) :
    (1 - ((54691280 + 368 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128) *
      sourceGoodMass (sharedFullGateTranscriptSamples adversary parameter auxiliary scalar.value witness fallback)
        (fun coin => PMF.pure coin.2.2) {coin | sharedFullCurveBad scalar.value coin}
        (table, selected, before, labels, decision, after) ≤
      (realAdaptiveTranscriptWithState sharedInternalCircuit
        (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary)
          (table, selected, before, labels, decision, after) := by
  rw [sharedFullCurveGood_weight_sum]
  exact sharedCurveSourcePhaseWeight_sum_real_le adversary parameter auxiliary scalar witness table
    referenceBefore referenceAfter selected labels decision before after key invalid bits mac
    firstCompatible secondCompatible encReference budget small lengthBound

end
end Kriterion.ArgoMAC.Security
