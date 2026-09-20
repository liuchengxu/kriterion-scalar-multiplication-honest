import Proof.Privacy.Source.Invalid.SharedInvalidHashEntrance
import Proof.Privacy.Source.Invalid.SharedCurveFullSourceMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 4096
attribute [local instance 10] Classical.propDecidable
attribute [local instance] bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
attribute [local irreducible] PMF.uniformOfFintype circuitMaskSampleGarble

/-- This projection retains the complete invalid source and its hidden bridge. -/
def sharedFullInvalidHashProjection {State : Type}
    (coin : Shared.Randomness × FullCircuitSource × SharedFullGateTranscript State) :
    Option (BaseField × SharedFullGateTranscript State) :=
  if FullSourceComplete coin.2.1.1 ∧ ¬ OnCurve coin.2.2.2.1.1 then
    some (coin.1.val.bridgeKey, coin.2.2) else none

/-- The invalid hash observer is exactly the full-source projection. -/
theorem actualSharedInvalidHashSource_eq_map [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) :
    actualSharedInvalidHashSource adversary parameter auxiliary scalar witness =
      (sharedFullGateTranscriptSamples adversary parameter auxiliary scalar witness fallback).map
        sharedFullInvalidHashProjection := by
  simp only [actualSharedInvalidHashSource, actualSharedFullGateSource, sharedFullGateTranscriptSamples,
    PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply congrArg (uniformRandomTape Shared.Randomness witness parameter).bind
  funext randomness
  apply congrArg₂ PMF.bind
  · apply congrArg (fun finite => @PMF.uniformOfFintype FullCircuitSource finite inferInstance)
    exact Subsingleton.elim _ _
  funext tag
  by_cases complete : FullSourceComplete tag.1
  · simp only [fullGateSourceRun, complete, if_true, retainedGateSourceRun, PMF.map_bind]
    apply congrArg (sharedGateSourceChoose adversary parameter auxiliary _ _).bind
    funext selected
    by_cases valid : OnCurve selected.1
    · simp only [sharedInvalidHashObserve, if_pos valid, sharedGateSourceObserve,
        PMF.map_comp, Function.comp_def, sharedFullInvalidHashProjection, complete, valid,
        not_true_eq_false, and_false, if_false, if_true]
      exact (PMF.map_const _ _).symm
    · simp only [sharedInvalidHashObserve, if_neg valid, sharedGateSourceObserve,
        PMF.map_comp, Function.comp_def, sharedFullInvalidHashProjection, complete, valid,
        not_false_eq_true, and_self, if_true]
      rfl
  · simp only [fullGateSourceRun, complete, if_false, sharedFullInvalidHashProjection,
      false_and, if_false]
    exact (PMF.map_const _ _).symm

/-- This bad event contains only complete invalid runs that query their hidden bridge. -/
def sharedFullInvalidHashHit {State : Type}
    (coin : Shared.Randomness × FullCircuitSource × SharedFullGateTranscript State) : Prop :=
  FullSourceComplete coin.2.1.1 ∧ ¬ OnCurve coin.2.2.2.1.1 ∧
    coin.1.val.bridgeKey ∈ transcriptHashInputs
      (sharedLegacyTranscript (coin.2.2.2.2.1 ++ coin.2.2.2.2.2.2.2))

/-- The full-source hidden-bridge event has the exact hash-observer probability. -/
theorem sharedFullInvalidHashHit_mass [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) :
    (sharedFullGateTranscriptSamples adversary parameter auxiliary scalar witness fallback).toOuterMeasure
      {coin | sharedFullInvalidHashHit coin} =
      (actualSharedInvalidHashSource adversary parameter auxiliary scalar witness).toOuterMeasure
        (sharedInvalidHashEvent (fun output => output.2.2.1 ++ output.2.2.2.2.2)) := by
  rw [actualSharedInvalidHashSource_eq_map adversary parameter auxiliary scalar witness fallback,
    PMF.toOuterMeasure_map_apply]
  congr 1
  ext coin
  change sharedFullInvalidHashHit coin ↔
    sharedFullInvalidHashProjection coin ∈ sharedInvalidHashEvent _
  have someHit (bridge : BaseField) (output : SharedFullGateTranscript adversary.State) :
      some (bridge, output) ∈ sharedInvalidHashEvent
        (fun output : SharedFullGateTranscript adversary.State => output.2.2.1 ++ output.2.2.2.2.2) ↔
      bridge ∈ transcriptHashInputs (sharedLegacyTranscript (output.2.2.1 ++ output.2.2.2.2.2)) := by
    constructor
    · rintro ⟨bridge', output', same, member⟩
      cases Option.some.inj same
      exact member
    · intro member
      exact ⟨bridge, output, rfl, member⟩
  by_cases complete : FullSourceComplete coin.2.1.1 <;> by_cases valid : OnCurve coin.2.2.2.1.1
  · simp only [sharedFullInvalidHashProjection, sharedFullInvalidHashHit, complete, valid,
      not_true_eq_false, and_false, false_and, if_false]
    simp [sharedInvalidHashEvent]
  · simpa only [sharedFullInvalidHashProjection, sharedFullInvalidHashHit, complete, valid,
      not_false_eq_true, and_self, true_and, if_true] using (someHit coin.1.val.bridgeKey coin.2.2).symm
  · simp only [sharedFullInvalidHashProjection, sharedFullInvalidHashHit, complete, false_and, if_false]
    simp [sharedInvalidHashEvent]
  · simp only [sharedFullInvalidHashProjection, sharedFullInvalidHashHit, complete, false_and, if_false]
    simp [sharedInvalidHashEvent]

/-- Complete invalid shared runs pay only the checked rounding and hidden-bridge losses. -/
theorem sharedFullInvalidHashHit_mass_le [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) :
    ((sharedFullGateTranscriptSamples adversary parameter auxiliary scalar witness fallback).toOuterMeasure
      {coin | sharedFullInvalidHashHit coin}).toReal ≤
      (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 +
      ((adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter : Nat) + 1 : ℝ) / baseFieldModulus := by
  rw [sharedFullInvalidHashHit_mass]
  exact actualSharedInvalidHashSource_mass_le adversary parameter auxiliary scalar witness

end
end Kriterion.ArgoMAC.Security
