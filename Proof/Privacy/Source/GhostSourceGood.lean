import Proof.Privacy.Source.FullGateGhostMass

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

private theorem goodPure_event {Source Transcript : Type*}
    (samples : PMF Source) (project : Source → Transcript) (bad : Set Source) (transcript : Transcript) :
    sourceGoodMass samples (fun source => PMF.pure (project source)) bad transcript =
      samples.toOuterMeasure {source | source ∉ bad ∧ project source = transcript} := by
  classical
  rw [sourceGoodMass, PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro source
  by_cases member : source ∈ bad
  · simp [member, Set.indicator]
  · by_cases equal : project source = transcript
    · simp [member, equal, Set.indicator]
    · simp [member, equal, Ne.symm equal, Set.indicator]

private theorem augmentedGood {Source Transcript : Type*}
    (samples : PMF Source) (kernel : Source → PMF Transcript) (bad : Set Source) (transcript : Transcript) :
    sourceGoodMass (samples.bind fun source => (kernel source).map (Prod.mk source))
      (fun pair => PMF.pure pair.2) (Prod.fst ⁻¹' bad) transcript =
      sourceGoodMass samples kernel bad transcript := by
  classical
  rw [goodPure_event, PMF.toOuterMeasure_bind_apply, sourceGoodMass]
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq, Set.mem_preimage]
  apply tsum_congr
  intro source
  by_cases member : source ∈ bad <;> simp [member, PMF.toOuterMeasure_apply_singleton]

private theorem ghostGood_le {Source Transcript Ghost : Type*}
    (samples : PMF Source) (kernel : Source → PMF Transcript) (ghost : PMF Ghost)
    (bad : Set Source) (extra : (Source × Transcript) × Ghost → Prop) (transcript : Transcript) :
    sourceGoodMass
      ((samples.bind fun source => (kernel source).map (Prod.mk source)).bind fun pair =>
        ghost.map (Prod.mk pair))
      (fun coin => PMF.pure coin.1.2) {coin | coin.1.1 ∈ bad ∨ extra coin} transcript ≤
      sourceGoodMass samples kernel bad transcript := by
  classical
  let joined := samples.bind fun source => (kernel source).map (Prod.mk source)
  have marginal : (joined.bind fun pair => ghost.map (Prod.mk pair)).map Prod.fst = joined := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    have each (pair : Source × Transcript) : ghost.map (fun _ => pair) = PMF.pure pair := PMF.map_const _ _
    simp_rw [each]
    exact PMF.bind_pure joined
  rw [← augmentedGood samples kernel bad transcript, goodPure_event, goodPure_event]
  change (joined.bind fun pair => ghost.map (Prod.mk pair)).toOuterMeasure _ ≤ joined.toOuterMeasure _
  conv_rhs => rw [← marginal, PMF.toOuterMeasure_map_apply]
  apply MeasureTheory.measure_mono
  rintro coin ⟨good, equal⟩
  exact ⟨fun member => good (Or.inl member), equal⟩

/-- The ghost restrictions only reduce the original prefix good mass. -/
theorem fullGateGhostGood_le_prefixGood [FieldCertificate] [GroupCertificate] [Fintype BaseField]
    {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : ScalarField) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State)) (transcript : FullGateTranscript adversary.State) :
    sourceGoodMass (fullGateGhostSamples adversary parameter auxiliary scalar witness fallback)
      (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin} transcript ≤
    sourceGoodMass
      (fullGatePrefixSamples scalar witness parameter
        (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2))
      (fullGatePrefixKernel scalar
        (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback) {coin | fullGatePrefixBad coin} transcript := by
  exact ghostGood_le _ _ (PMF.uniformOfFintype BaseField) _
    (fun coin => HiddenLinkBad (fullGateGhostResult coin.1.1)
      (coin.1.2.2.2.1 ++ coin.1.2.2.2.2.2.2) coin.2) transcript

end

end Kriterion.ArgoMAC.Security
