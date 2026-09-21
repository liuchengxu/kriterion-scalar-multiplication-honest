import Proof.Privacy.SharedConcreteAdaptivePrivacy
import Proof.Privacy.Source.Valid.SharedPipelineSourceView
import Proof.Privacy.Source.Invalid.SharedCurveSourceView
import Proof.Privacy.Transcript.SharedGateEndpoint

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions OperationalOracle
noncomputable section
attribute [local instance 10] Classical.propDecidable
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] sharedRetainedPipelineCommands retainedFullTable circuitMaskSampleGarble PMF.uniformOfFintype

/-- The strict source stops when checked programming reports a used pair. -/
def sharedStrictGateSourceObserve {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table)
    (selected : AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))
    (view : SelectedGateView) (data : GarblingOracleData) : PMF Bool :=
  let labels := sourceInputLabels data selected.1
  let final := sharedProgramSelectedGateView selected.2.2.1 selected.1 labels.inputMac view
  if final.bad then PMF.pure false
  else (adversary.decide parameter table labels auxiliary selected.2.1).run idealOracleHandler final |>.map Prod.fst

theorem sharedStrictGateSourceObserve_good {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table)
    (selected : AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))
    (view : SelectedGateView) (data : GarblingOracleData)
    (good : (sharedProgramSelectedGateView selected.2.2.1 selected.1
      (sourceInputLabels data selected.1).inputMac view).bad = false) :
    sharedStrictGateSourceObserve adversary parameter auxiliary table selected view data =
      (sharedGateSourceObserve adversary parameter auxiliary table selected view data).map
        (fun transcript => transcript.2.2.2.2.1) := by
  simp only [sharedStrictGateSourceObserve, good, Bool.false_eq_true, if_false,
    sharedGateSourceObserve, PMF.map_comp, Function.comp_def]
  have erased := congrArg (PMF.map Prod.fst) (runOracleProgramWithTranscript_erase idealOracleHandler
    (adversary.decide parameter table (sourceInputLabels data selected.1) auxiliary selected.2.1)
    (sharedProgramSelectedGateView selected.2.2.1 selected.1 (sourceInputLabels data selected.1).inputMac view))
  simpa only [PMF.map_comp, Function.comp_def] using erased.symm

/-- The source entrance bound also covers strict programming failure. -/
theorem sharedStrictGateSource_entrance [FieldCertificate] [GroupCertificate] [TerminationCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Bool)
    (event : Set Bool) :
    |((actualSharedFullGateSource scalar witness parameter
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
        (fun table selected view rest => sharedStrictGateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback).toOuterMeasure event).toReal -
      ((actualSharedIdealGateSourceRun scalar
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
        (fun table selected view rest => sharedStrictGateSourceObserve adversary parameter auxiliary table selected view rest.2)).toOuterMeasure event).toReal| ≤
      (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 + (2 : ℝ) ^ (-240 : ℤ) :=
  actualSharedGateSource_observation_bound scalar witness parameter _ _ fallback event

/-- The existing pipeline guard also prevents strict abort on the invalid branch. -/
theorem sharedStrictSelectedView_good [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey) (tag : FullCircuitSource)
    (state : Shared.Simulator.OracleState)
    (good : SharedPipelineTagGood rest keys table input key state tag)
    (initial : state.bad = false)
    (enc : state.encOracle = rest.encPRFOracle) (hash : state.hashOracle = rest.hashOracle) :
    (sharedProgramSelectedGateView state input (key.encodeAffine input)
      (selectedGateView (circuitMaskSampleGarble rest.algebraic.field.bridgeKey
        rest.algebraic.field.curveMask.value
        (FieldMacToECMac.rowsForOutputKeys keys rest.algebraic.point.pointRandomness)
        input (retainedFullSource rest tag)) input)).bad = false := by
  by_cases valid : OnCurve input
  · rw [sharedValidSourceView_program rest keys input key tag state valid enc hash]
    exact (sharedCommands_bad_fresh state _ good.2.2.2).trans initial
  · rw [sharedInvalidSourceView_program rest keys input key tag state valid]
    exact (sharedCommands_bad_fresh state _
      (sharedPipelineFresh_curve rest keys input key tag state.fixedTranscript good.2.2.2)).trans initial

private theorem transcriptFinal_bad (state : Shared.Simulator.OracleState)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    (transcriptFinalState idealOracleHandler state transcript).bad = state.bad := by
  induction transcript generalizing state with
  | nil => rfl
  | cons entry rest ih =>
    rw [transcriptFinalState, ih]
    cases entry.1 <;> rfl

/-- This ghost flag records only a checked programming failure in a complete source. -/
def sharedPrefixAbort [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField)
    (coin : Shared.Randomness × FullCircuitSource ×
      (AffineInput × (State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))) : Bool :=
  let retained := maskRetainedTape coin.1.val
  let source := (coin.2.1.1, sharedCircuitHashRest coin.1.val coin.2.1.2)
  if FullSourceComplete source.1 then
    let selected := coin.2.2
    let rows := retainedSourceRows scalar retained
    let view := selectedGateView (circuitMaskSampleGarble retained.2.2.1.1 retained.2.2.1.2.value rows
      selected.1 (decodeFullSource source)) selected.1
    (sharedProgramSelectedGateView selected.2.2.1 selected.1
      (sourceInputLabels retained.2.2.2 selected.1).inputMac view).bad
  else false

/-- Every supported good source prefix gives the old decision without a strict abort. -/
theorem sharedPrefixAbort_retained_good [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (rest : GarblingSourceRest) (sample : PermutationOracle Shared.FixedKeyIndex Block × InputMacKey)
    (tag : FullCircuitSource)
    (selected : AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))
    (member : selected ∈ (sharedGateSourceChoose adversary parameter auxiliary
      (retainedFullTable rest (FieldMacToECMac.outputKeys construction scalar rest.reference.offsets) tag)
      ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩).support)
    (good : ¬ sharedFullPipelinePrefixBad scalar (sharedGarblingOracleKeyEquiv.symm (sample, rest), tag, selected)) :
    sharedPrefixAbort scalar (sharedGarblingOracleKeyEquiv.symm (sample, rest), tag, selected) = false := by
  rw [sharedFullPipelinePrefixBad_oracleKey] at good
  have valid := Classical.not_not.mp good
  have final := (sharedGateSourceChoose_final adversary parameter auxiliary _ _ selected member).1
  rw [← final] at valid
  have oracles := sharedGateSourceChoose_oracles adversary parameter auxiliary _ _ selected member
  have initial : selected.2.2.1.bad = false := by
    rw [final, transcriptFinal_bad]
    rfl
  have checked := sharedStrictSelectedView_good rest _ _ selected.1 sample.2 tag selected.2.2.1
    valid initial oracles.2.1 oracles.2.2
  simp only [sharedPrefixAbort, valid.1, if_true,
    retainedSourceRows_sharedOracleKey, sharedCircuitHashRest_sharedOracleKey,
    maskRetainedTape_sharedOracleKey_data]
  exact checked


theorem sharedStrictObserve_abort {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table)
    (selected : AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))
    (view : SelectedGateView) (data : GarblingOracleData) :
    sharedStrictGateSourceObserve adversary parameter auxiliary table selected view data =
      if (sharedProgramSelectedGateView selected.2.2.1 selected.1
          (sourceInputLabels data selected.1).inputMac view).bad then PMF.pure false
      else (sharedGateSourceObserve adversary parameter auxiliary table selected view data).map
        (fun transcript => transcript.2.2.2.2.1) := by
  split
  · rename_i bad
    simp only [sharedStrictGateSourceObserve, bad, if_true]
  · rename_i good
    rw [sharedStrictGateSourceObserve_good adversary parameter auxiliary table selected view data
      (Bool.eq_false_of_not_eq_true good)]

theorem sharedStrictPrefixKernel_abort [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (coin : Shared.Randomness × FullCircuitSource ×
      (AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer))))
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) :
    sharedFullGatePrefixKernel scalar
      (fun table selected view rest => sharedStrictGateSourceObserve adversary parameter auxiliary table selected view rest.2)
      (fun retained source => (fallback retained source).map (fun transcript => transcript.2.2.2.2.1)) coin =
      if sharedPrefixAbort scalar coin then PMF.pure false
      else (sharedFullGatePrefixKernel scalar
        (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback coin).map (fun transcript => transcript.2.2.2.2.1) := by
  classical
  simp only [sharedFullGatePrefixKernel, fullGatePrefixKernel, sharedPrefixAbort]
  split
  · exact sharedStrictObserve_abort adversary parameter auxiliary _ _ _ _
  · simp

/-- The original combined good event excludes every strict programming abort. -/
theorem sharedPrefixAbort_good [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (coin : Shared.Randomness × FullCircuitSource ×
      (AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer))))
    (member : coin ∈ (sharedFullGatePrefixSamples scalar witness parameter
      (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)).support)
    (good : ¬ sharedFullPipelinePrefixBad scalar coin) : sharedPrefixAbort scalar coin = false := by
  simp only [sharedFullGatePrefixSamples, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at member
  obtain ⟨randomness, _, tag, _, selected, supported, rfl⟩ := member
  obtain ⟨⟨sample, rest⟩, rfl⟩ := sharedGarblingOracleKeyEquiv.symm.surjective randomness
  rw [← retainedFullTable_sharedPrefixTable scalar rest sample tag, maskRetainedTape_sharedOracleKey_data] at supported
  exact sharedPrefixAbort_retained_good adversary parameter auxiliary scalar rest sample tag selected supported good

/-- The replacement transcript records the strict failure as a false decision. -/
def sharedStrictTranscript [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField)
    (coin : (Shared.Randomness × FullCircuitSource ×
      (AffineInput × (State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))) ×
        SharedFullGateTranscript State) : SharedFullGateTranscript State :=
  let transcript := coin.2
  if sharedPrefixAbort scalar coin.1 then
    (transcript.1, transcript.2.1, transcript.2.2.1, transcript.2.2.2.1, false, transcript.2.2.2.2.2)
  else transcript

theorem sharedStrictTranscript_good [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State))
    (coin) (member : coin ∈ (sharedCombinedSource adversary parameter auxiliary scalar witness fallback).support)
    (good : ¬ sharedCombinedBad scalar coin) : sharedStrictTranscript scalar coin = coin.2 := by
  simp only [sharedCombinedSource, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at member
  obtain ⟨prior, supported, output, _, rfl⟩ := member
  have noAbort := sharedPrefixAbort_good adversary parameter auxiliary scalar witness prior supported
    (fun bad => good (Or.inl bad))
  simp [sharedStrictTranscript, noAbort]

theorem sharedStrictTranscript_decision [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) :
    ((sharedCombinedSource adversary parameter auxiliary scalar witness fallback).map
      (sharedStrictTranscript scalar)).map (fun transcript => transcript.2.2.2.2.1) =
    actualSharedFullGateSource scalar witness parameter
      (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
      (fun table selected view rest => sharedStrictGateSourceObserve adversary parameter auxiliary table selected view rest.2)
      (fun retained source => (fallback retained source).map (fun transcript => transcript.2.2.2.2.1)) := by
  rw [← sharedFullGatePrefixSamples_bind]
  simp only [sharedCombinedSource, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply PMF.bind_congr
  intro coin _
  rw [sharedStrictPrefixKernel_abort]
  cases abort : sharedPrefixAbort scalar coin <;>
    simp only [sharedStrictTranscript, abort, Bool.false_eq_true, if_false, if_true]
  exact PMF.map_const _ _

/-- Strict programming uses the same bad event and the same error budget. -/
theorem sharedStrictAdaptive_event_bound [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) (prefixBound : ℝ)
    (prefixMass : ((sharedFullGatePrefixSamples scalar.value witness parameter
      (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)).toOuterMeasure
        {coin | sharedFullPipelinePrefixBad scalar.value coin}).toReal ≤ prefixBound)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter ≤ 2 ^ 101)
    (event : Set Bool) :
    |((realAdaptiveTranscriptWithState sharedInternalCircuit
        (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary).toOuterMeasure
          {transcript | transcript.2.2.2.2.1 ∈ event}).toReal -
      ((actualSharedIdealGateSourceRun scalar.value
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
        (fun table selected view rest => sharedStrictGateSourceObserve adversary parameter auxiliary table selected view rest.2)).toOuterMeasure event).toReal| ≤
      prefixBound + (54691280 + 368 * (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) : ℝ) / 2 ^ 128 +
      ((adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter : Nat) + 1 : ℝ) / baseFieldModulus +
      2 * (278638 * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384) + (2 : ℝ) ^ (-240 : ℤ) := by
  have bad := sharedCombinedBad_real_mass_le adversary parameter auxiliary scalar.value witness fallback prefixBound prefixMass
  have ratio := hCoefficient_event_of_sourceGoodMass_congr
    (realAdaptiveTranscriptWithState sharedInternalCircuit (uniformRandomTape Shared.Randomness witness)
      sharedRealOracleHandler adversary parameter scalar auxiliary)
    (sharedCombinedSource adversary parameter auxiliary scalar.value witness fallback)
    (fun coin => PMF.pure coin.2) (fun coin => PMF.pure (sharedStrictTranscript scalar.value coin))
    {coin | sharedCombinedBad scalar.value coin}
    (((54691280 + 368 * (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) : Nat) : ENNReal) /
      (2 : ENNReal) ^ 128) (by finiteness) _ bad
    (fun output => sharedCombinedGood_real_le adversary parameter auxiliary scalar witness fallback output small)
    (by intro coin supported good; rw [sharedStrictTranscript_good adversary parameter auxiliary scalar.value witness fallback coin supported good])
    {transcript | transcript.2.2.2.2.1 ∈ event}
  have projection := congrArg (fun distribution : PMF Bool => (distribution.toOuterMeasure event).toReal)
    (sharedStrictTranscript_decision adversary parameter auxiliary scalar.value witness fallback)
  simp only [PMF.toOuterMeasure_map_apply] at projection
  have mapped : (sharedCombinedSource adversary parameter auxiliary scalar.value witness fallback).bind
      (fun coin => PMF.pure (sharedStrictTranscript scalar.value coin)) =
      (sharedCombinedSource adversary parameter auxiliary scalar.value witness fallback).map
        (sharedStrictTranscript scalar.value) := PMF.bind_pure_comp _ _
  rw [mapped, PMF.toOuterMeasure_map_apply] at ratio
  simp only [Set.preimage, Set.mem_ofPred_eq] at projection ratio
  rw [projection] at ratio
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat] at ratio
  have entrance := sharedStrictGateSource_entrance adversary parameter auxiliary scalar.value witness
    (fun retained source => (fallback retained source).map (fun transcript => transcript.2.2.2.2.1)) event
  have combined := (abs_sub_le
    ((realAdaptiveTranscriptWithState sharedInternalCircuit (uniformRandomTape Shared.Randomness witness)
      sharedRealOracleHandler adversary parameter scalar auxiliary).toOuterMeasure
        {transcript | transcript.2.2.2.2.1 ∈ event}).toReal
    ((actualSharedFullGateSource scalar.value witness parameter
      (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
      (fun table selected view rest => sharedStrictGateSourceObserve adversary parameter auxiliary table selected view rest.2)
      (fun retained source => (fallback retained source).map (fun transcript => transcript.2.2.2.2.1))).toOuterMeasure event).toReal
    ((actualSharedIdealGateSourceRun scalar.value
      (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
      (fun table selected view rest => sharedStrictGateSourceObserve adversary parameter auxiliary table selected view rest.2)).toOuterMeasure event).toReal).trans
      (add_le_add ratio entrance)
  convert combined using 1 <;> push_cast
  all_goals first | rfl | ring

/-- Every strict shared source decision satisfies the original adaptive envelope. -/
theorem sharedStrictAdaptiveAdvantage_envelope [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter ≤ 2 ^ 101) :
    advantage
      (GarbledCircuit.realGame sharedInternalCircuit (uniformRandomTape Shared.Randomness witness)
        sharedRealOracleHandler adversary parameter scalar auxiliary)
      (actualSharedIdealGateSourceRun scalar.value
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
        (fun table selected view rest => sharedStrictGateSourceObserve adversary parameter auxiliary table selected view rest.2)) ≤
      adaptiveErrorEnvelope (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) := by
  letI : Fintype Block := Fintype.ofFinite Block
  have bound := sharedStrictAdaptive_event_bound adversary parameter auxiliary scalar witness
    (fun _ _ => realAdaptiveTranscriptWithState sharedInternalCircuit
      (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary)
    _ (sharedFullPipelinePrefixBad_mass_le adversary parameter auxiliary scalar.value witness) small {true}
  have realDecision : (realAdaptiveTranscriptWithState sharedInternalCircuit
      (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary).map
      (fun output => output.2.2.2.2.1) =
      GarbledCircuit.realGame sharedInternalCircuit (uniformRandomTape Shared.Randomness witness)
        sharedRealOracleHandler adversary parameter scalar auxiliary := by
    rw [← realAdaptiveTranscript_decision sharedInternalCircuit _ _ adversary parameter scalar auxiliary,
      ← realAdaptiveTranscriptWithState_erase sharedInternalCircuit _ _ adversary parameter scalar auxiliary,
      PMF.map_comp]
    rfl
  unfold advantage
  rw [← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton,
    ← realDecision, PMF.toOuterMeasure_map_apply]
  apply bound.trans
  have accounting := sharedAdaptiveThreeRoundingLossSum_le_envelope
    (adversary.firstQueryBudget parameter)
    (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) (Nat.le_add_right _ _)
  convert accounting using 1 <;> first | rfl |
    (simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]; ring)

end
end Kriterion.ArgoMAC.Security
