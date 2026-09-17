import Proof.Privacy.Transcript.AdaptiveTranscriptLength
import Proof.Privacy.Collision.HiddenLinkBad

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev FullGateTranscript (State : Type) :=
  Pipeline.Table × (AffineInput × State) × List (Sigma Garbling.oracleSpec.Answer) ×
    Garbling.Labels × Bool × List (Sigma Garbling.oracleSpec.Answer)

abbrev FullGatePrefixCoin (State : Type) :=
  Garbling.Randomness × ((RawCircuitGate → FullHashLift) × CircuitMaskTables) ×
    (AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))

/-- This normalized source keeps the prefix coin and its complete continuation. -/
def fullGateTranscriptSamples [Fintype BaseField] [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : ScalarField) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State)) :
    PMF (FullGatePrefixCoin adversary.State × FullGateTranscript adversary.State) :=
  (fullGatePrefixSamples scalar witness parameter
    (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2)).bind fun sample =>
      (fullGatePrefixKernel scalar
        (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback sample).map (Prod.mk sample)

/-- This augmentation samples one independent field key after a complete source. -/
def ghostAugment [Fintype BaseField] {Source : Type*} (samples : PMF Source) : PMF (Source × BaseField) :=
  samples.bind fun source => (PMF.uniformOfFintype BaseField).map (Prod.mk source)

/-- The ghost key is independent of the complete source transcript. -/
def fullGateGhostSamples [Fintype BaseField] [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : ScalarField) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State)) :=
  ghostAugment (fullGateTranscriptSamples adversary parameter auxiliary scalar witness fallback)

/-- The selected curve result determines the excluded zero-mask diagonal. -/
def fullGateGhostResult {State : Type} (sample : FullGatePrefixCoin State) : BaseField :=
  sample.1.bridgeKey + sample.1.curveMask.value *
    (sample.2.2.1.x ^ 3 + 3 - sample.2.2.1.y ^ 2)

/-- The good source excludes prefix faults and full-transcript ghost hits. -/
def fullGateGhostBad [Fintype BaseField] [FieldCertificate] [GroupCertificate] {State : Type}
    (coin : (FullGatePrefixCoin State × FullGateTranscript State) × BaseField) : Prop :=
  fullGatePrefixBad coin.1.1 ∨ HiddenLinkBad (fullGateGhostResult coin.1.1)
    (coin.1.2.2.2.1 ++ coin.1.2.2.2.2.2.2) coin.2

private theorem augmented_first {A B : Type*} (samples : PMF A) (kernel : A → PMF B) :
    (samples.bind fun a => (kernel a).map (Prod.mk a)).map Prod.fst = samples := by
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  have each (a : A) : (kernel a).map (fun _ => a) = PMF.pure a := PMF.map_const _ _
  simp_rw [each]
  exact PMF.bind_pure samples

private theorem augmented_second {A B : Type*} (samples : PMF A) (kernel : A → PMF B) :
    (samples.bind fun a => (kernel a).map (Prod.mk a)).map Prod.snd = samples.bind kernel := by
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply congrArg samples.bind
  funext a
  exact PMF.map_id (kernel a)

/-- Removing the ghost and prefix coin restores the exact full source transcript. -/
theorem fullGateGhostSamples_transcript [Fintype BaseField] [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : ScalarField) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State)) :
    (fullGateGhostSamples adversary parameter auxiliary scalar witness fallback).map (fun coin => coin.1.2) =
      fullAdaptiveGateSource scalar witness parameter
        (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2)
        (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback := by
  rw [show (fun coin : (FullGatePrefixCoin adversary.State × FullGateTranscript adversary.State) × BaseField =>
    coin.1.2) = Prod.snd ∘ Prod.fst from rfl, ← PMF.map_comp]
  rw [fullGateGhostSamples, ghostAugment, augmented_first, fullGateTranscriptSamples, augmented_second,
    fullGatePrefixSamples_bind]

/-- The complete normalized transcript source obeys the declared query budget. -/
theorem fullGateTranscriptSamples_length [Fintype BaseField] [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : ScalarField) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State))
    (fallbackLength : ∀ retained source output, output ∈ (fallback retained source).support →
      (output.2.2.1 ++ output.2.2.2.2.2).length ≤
        adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter)
    (coin : FullGatePrefixCoin adversary.State × FullGateTranscript adversary.State)
    (member : coin ∈ (fullGateTranscriptSamples adversary parameter auxiliary scalar witness fallback).support) :
    (coin.2.2.2.1 ++ coin.2.2.2.2.2.2).length ≤
      adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter := by
  simp only [fullGateTranscriptSamples, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at member
  obtain ⟨sample, sampleMember, output, outputMember, rfl⟩ := member
  exact fullGatePrefixKernel_length_le adversary parameter auxiliary scalar witness fallback fallbackLength
    sample sampleMember output outputMember


/-- Removing the continuation and ghost restores the exact prefix source. -/
theorem fullGateGhostSamples_prefix [Fintype BaseField] [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : ScalarField) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State)) :
    (fullGateGhostSamples adversary parameter auxiliary scalar witness fallback).map (fun coin => coin.1.1) =
      fullGatePrefixSamples scalar witness parameter
        (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2) := by
  rw [show (fun coin : (FullGatePrefixCoin adversary.State × FullGateTranscript adversary.State) × BaseField =>
    coin.1.1) = Prod.fst ∘ Prod.fst from rfl, ← PMF.map_comp]
  rw [fullGateGhostSamples, ghostAugment, augmented_first, fullGateTranscriptSamples, augmented_first]

private theorem pmf_mass_finite {A : Type*} (p : PMF A) (event : Set A) :
    p.toOuterMeasure event ≠ ⊤ := by
  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  calc
    _ ≤ p.toOuterMeasure Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
    _ = 1 := (p.toOuterMeasure_apply_eq_one_iff _).mpr (Set.subset_univ _)

private theorem pmf_union_real {A : Type*} (p : PMF A) (first second : Set A) :
    (p.toOuterMeasure (first ∪ second)).toReal ≤
      (p.toOuterMeasure first).toReal + (p.toOuterMeasure second).toReal := by
  have bound := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨pmf_mass_finite p first, pmf_mass_finite p second⟩)
    (MeasureTheory.measure_union_le (μ := p.toOuterMeasure) first second)
  rwa [ENNReal.toReal_add (pmf_mass_finite p first) (pmf_mass_finite p second)] at bound

private theorem hiddenLinkLoss_finite (budget : Nat) :
    ((1 + budget : ℝ≥0∞) / baseFieldModulus) ≠ ⊤ := by
  norm_num [baseFieldModulus]
  finiteness

private theorem hiddenLinkLoss_toReal (budget : Nat) :
    ((1 + budget : ℝ≥0∞) / baseFieldModulus).toReal = (1 + budget : ℝ) / baseFieldModulus := by
  rw [ENNReal.toReal_div, ENNReal.toReal_add (by simp) (by simp)]
  simp

private theorem normalizedGhostBad_mass_le [Fintype BaseField] {Source : Type*}
    (samples : PMF Source) (bad : Set Source) (curveResult : Source → BaseField)
    (history : Source → List (Sigma Garbling.oracleSpec.Answer)) (budget : Nat)
    (lengthBound : ∀ source ∈ samples.support, (history source).length ≤ budget) :
    (((ghostAugment samples).toOuterMeasure
      {coin | coin.1 ∈ bad ∨ HiddenLinkBad (curveResult coin.1) (history coin.1) coin.2})).toReal ≤
      (samples.toOuterMeasure bad).toReal + (1 + budget : ℝ) / baseFieldModulus := by
  let joint := ghostAugment samples
  have first := congrArg (fun distribution => (distribution.toOuterMeasure bad).toReal)
    (augmented_first samples (fun _ => PMF.uniformOfFintype BaseField))
  simp only [PMF.toOuterMeasure_map_apply] at first
  have bound := hiddenLinkBad_source_mass_le samples curveResult history budget lengthBound
  have realBound := (ENNReal.toReal_mono (hiddenLinkLoss_finite budget) bound).trans_eq
    (hiddenLinkLoss_toReal budget)
  have union := pmf_union_real joint (Prod.fst ⁻¹' bad)
    {coin | HiddenLinkBad (curveResult coin.1) (history coin.1) coin.2}
  apply union.trans
  apply add_le_add
  · exact first.le
  · dsimp only [joint, ghostAugment]
    exact realBound

set_option maxRecDepth 2048 in
/-- The normalized ghost event pays one full-transcript exclusion bound. -/
theorem fullGateGhostBad_mass_le [Fintype BaseField] [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : ScalarField) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State))
    (fallbackLength : ∀ retained source output, output ∈ (fallback retained source).support →
      (output.2.2.1 ++ output.2.2.2.2.2).length ≤
        adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) :
    ((fullGateGhostSamples adversary parameter auxiliary scalar witness fallback).toOuterMeasure
      {coin | fullGateGhostBad coin}).toReal ≤
      (224668080 / (2 : ℝ) ^ 128 +
        (182 * adversary.firstQueryBudget parameter : Nat) / (2 : ℝ) ^ 128 +
        (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384) +
      (1 + (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter : Nat)) /
        (baseFieldModulus : ℝ) := by
  have first := congrArg (fun distribution =>
    (distribution.toOuterMeasure {sample | fullGatePrefixBad sample}).toReal)
    (augmented_first
      (fullGatePrefixSamples scalar witness parameter
        (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2))
      (fullGatePrefixKernel scalar
        (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback))
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] at first
  have prefixBound := fullGatePrefixBad_mass_le adversary parameter auxiliary scalar witness
  have bound := normalizedGhostBad_mass_le
    (fullGateTranscriptSamples adversary parameter auxiliary scalar witness fallback)
    {coin | fullGatePrefixBad coin.1} (fun coin => fullGateGhostResult coin.1)
    (fun coin => coin.2.2.2.1 ++ coin.2.2.2.2.2.2)
    (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter)
    (fullGateTranscriptSamples_length adversary parameter auxiliary scalar witness fallback fallbackLength)
  have result := bound.trans (add_le_add_left (first.le.trans prefixBound) _)
  simpa only [fullGateGhostSamples, fullGateGhostBad, Set.mem_setOf_eq] using result


/-- The missing augmented good mass is one normalized bad-source probability. -/
theorem fullGateGhostGood_missing_le [Fintype BaseField] [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : ScalarField) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State))
    (fallbackLength : ∀ retained source output, output ∈ (fallback retained source).support →
      (output.2.2.1 ++ output.2.2.2.2.2).length ≤
        adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) :
    let samples := fullGateGhostSamples adversary parameter auxiliary scalar witness fallback
    let kernel := fun coin : (FullGatePrefixCoin adversary.State × FullGateTranscript adversary.State) × BaseField =>
      PMF.pure coin.1.2
    (∑' transcript : FullGateTranscript adversary.State,
      ((fullAdaptiveGateSource scalar witness parameter
        (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2)
        (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback) transcript - sourceGoodMass samples kernel {coin | fullGateGhostBad coin} transcript)).toReal ≤
      (224668080 / (2 : ℝ) ^ 128 +
        (182 * adversary.firstQueryBudget parameter : Nat) / (2 : ℝ) ^ 128 +
        (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384) +
      (1 + (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter : Nat)) /
        (baseFieldModulus : ℝ) := by
  dsimp only
  have law := fullGateGhostSamples_transcript adversary parameter auxiliary scalar witness fallback
  change ((fullGateGhostSamples adversary parameter auxiliary scalar witness fallback).bind
    (fun coin => PMF.pure coin.1.2)) = _ at law
  rw [← law, sourceGoodMass_missing]
  exact fullGateGhostBad_mass_le adversary parameter auxiliary scalar witness fallback fallbackLength


/-- The real transcript is a normalized fallback with the same adversary state type. -/
def fullGateRealFallback [Fintype BaseField] [FieldCertificate] [GroupCertificate] [TerminationCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : NonZeroScalar) (witness : Garbling.Randomness) :
    MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State) :=
  fun _ _ => realAdaptiveTranscriptWithState (Garbling.garbledCircuit construction)
    (randomTape witness) Garbling.oracleHandler adversary parameter scalar auxiliary

/-- The concrete real fallback obeys the complete adaptive query budget. -/
theorem fullGateRealFallback_length [Fintype BaseField] [FieldCertificate] [GroupCertificate] [TerminationCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : NonZeroScalar) (witness : Garbling.Randomness)
    (retained : MaskRetainedTape) (source : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (output : FullGateTranscript adversary.State)
    (member : output ∈ (fullGateRealFallback adversary parameter auxiliary scalar witness retained source).support) :
    (output.2.2.1 ++ output.2.2.2.2.2).length ≤
      adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter := by
  exact realAdaptiveTranscriptWithState_length_le (Garbling.garbledCircuit construction)
    (randomTape witness) Garbling.oracleHandler adversary parameter scalar auxiliary output member


end
end Kriterion.ArgoMAC.Security
