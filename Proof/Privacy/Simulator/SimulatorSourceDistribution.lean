import Proof.Privacy.Source.AdaptiveGateSourceDistribution

namespace Kriterion.ArgoMAC.Security

open BN254 FieldMacToECMac Cryptography

noncomputable section

attribute [local instance] xRandomnessFintype yRandomnessFintype zRandomnessFintype

local instance : Nonempty SourceOracleRest := ⟨outputSourceOracleRest (Classical.arbitrary OutputRowRest)⟩
local instance : Nonempty PublicSample := ⟨defaultSimulatorCoin.tableSample⟩
local instance : Nonempty SimulatorCoin := ⟨defaultSimulatorCoin⟩
local instance : Nonempty NonZeroBase := ⟨(Seed.randomness 0).curveMask⟩

/-- This split removes exactly the unused field randomizers from the output rest. -/
def outputOracleRestEquiv : OutputRowRest ≃
    ((Fin outputMacCount → Biquadratic.XRandomness × Biquadratic.YRandomness × Biquadratic.ZRandomness) ×
      (BaseField × BaseField)) × SourceOracleRest where
  toFun rest := ((rest.1, rest.2.1.curveR1, rest.2.1.curveR2), outputSourceOracleRest rest)
  invFun sample := (sample.1.1,
    ⟨sample.2.1.1, sample.2.1.2, sample.1.2.1, sample.1.2.2⟩, sample.2.2)
  left_inv rest := by rcases rest with ⟨rows, ⟨key, mask, first, second⟩, oracles⟩; rfl
  right_inv sample := rfl

/-- The retained key, mask, and oracle source has its exact uniform marginal. -/
theorem map_uniform_outputSourceOracleRest :
    (PMF.uniformOfFintype OutputRowRest).map outputSourceOracleRest =
      PMF.uniformOfFintype SourceOracleRest := by
  have law := congrArg (fun distribution => distribution.map Prod.snd)
    (map_uniformOfFintype_equivBetween outputOracleRestEquiv)
  rw [PMF.map_comp, map_uniform_prod_snd] at law
  exact law

/-- This source keeps the exact simulator coin and the unused nonzero curve mask. -/
def simulatorSourceEquiv : (SourceOracleRest × PublicSample) ≃ SimulatorCoin × NonZeroBase where
  toFun sample := (⟨sample.2,
    ⟨sample.1.2.fixedKeyOracle, sample.1.2.encPRFOracle, sample.1.2.hashOracle⟩,
    sample.1.2.inputMacKey, sample.1.1.1⟩, sample.1.1.2)
  invFun sample := (((sample.1.bridgeKey, sample.2),
    ⟨sample.1.oracles.fixedOracle, sample.1.inputKey, sample.1.oracles.encOracle,
      sample.1.oracles.hashOracle⟩), sample.1.tableSample)
  left_inv sample := by
    rcases sample with ⟨⟨⟨key, mask⟩, ⟨fixed, inputKey, enc, hash⟩⟩, table⟩
    rfl
  right_inv sample := by
    rcases sample with ⟨⟨table, ⟨fixed, enc, hash⟩, inputKey, key⟩, mask⟩
    rfl

/-- The retained source and public sample give the exact offline simulator coin. -/
theorem map_uniform_simulatorSource :
    (PMF.uniformOfFintype (SourceOracleRest × PublicSample)).map simulatorSourceEquiv =
      PMF.uniformOfFintype (SimulatorCoin × NonZeroBase) :=
  map_uniformOfFintype_equivBetween simulatorSourceEquiv

/-- This identity retains any observation of the source and public sample. -/
theorem bind_uniform_simulatorSource {Observation : Type*}
    (observe : SourceOracleRest → PublicSample → PMF Observation) :
    (PMF.uniformOfFintype OutputRowRest).bind (fun rest =>
      (PMF.uniformOfFintype PublicSample).bind (observe (outputSourceOracleRest rest))) =
    (PMF.uniformOfFintype (SimulatorCoin × NonZeroBase)).bind (fun coin =>
      observe (simulatorSourceEquiv.symm coin).1 (simulatorSourceEquiv.symm coin).2) := by
  have marginal := congrArg (fun distribution => distribution.bind (fun rest =>
    (PMF.uniformOfFintype PublicSample).bind (observe rest)))
    map_uniform_outputSourceOracleRest
  simp only [PMF.bind_map, Function.comp_def] at marginal
  rw [marginal]
  have source := congrArg (fun distribution => distribution.bind (fun coin =>
    observe (simulatorSourceEquiv.symm coin).1 (simulatorSourceEquiv.symm coin).2))
    map_uniform_simulatorSource
  simp only [PMF.bind_map, Function.comp_def] at source
  simp only [Equiv.symm_apply_apply] at source
  rw [← source, uniform_prod_eq_bind (First := SourceOracleRest) (Second := PublicSample),
    PMF.bind_bind]
  simp only [PMF.bind_map]
  exact PMF.bind_comm _ _ _

/-- This change of variables keeps the public sample and every oracle. -/
def sourceSelectedCurveShift (input : AffineInput) :
    (SourceOracleRest × PublicSample) ≃ (SourceOracleRest × PublicSample) where
  toFun source := (((source.1.1.1 + source.1.1.2.value * (input.x ^ 3 + 3 - input.y ^ 2),
    source.1.1.2), source.1.2), source.2)
  invFun source := (((source.1.1.1 - source.1.1.2.value * (input.x ^ 3 + 3 - input.y ^ 2),
    source.1.1.2), source.1.2), source.2)
  left_inv source := by simp
  right_inv source := by simp

/-- The adaptive key shift preserves every observation that uses only its selected result. -/
theorem sourceSelectedCurveShift_run {Aux Observation : Type*}
    (choose : Pipeline.Table → GarblingOracleData → PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → (SourceOracleRest × PublicSample) → PMF Observation) :
    (PMF.uniformOfFintype (SourceOracleRest × PublicSample)).bind (fun source =>
      (choose (publicMaskTable source.2) source.1.2).bind fun selected =>
        observe selected (sourceSelectedCurveShift selected.1 source)) =
    (PMF.uniformOfFintype (SourceOracleRest × PublicSample)).bind (fun source =>
      (choose (publicMaskTable source.2) source.1.2).bind fun selected =>
        observe selected source) := by
  exact uniform_bind_viewEquiv_observe (fun selected : AffineInput × Aux =>
    sourceSelectedCurveShift selected.1)
    (fun source => (publicMaskTable source.2, source.1.2))
    (fun source => (publicMaskTable source.2, source.1.2))
    (fun _ _ => rfl) (fun view => choose view.1 view.2) observe

/-- This joint source removes only the obsolete output randomizers. -/
theorem bind_uniform_outputSourceJoint {Observation : Type*}
    (observe : SourceOracleRest → PublicSample → PMF Observation) :
    (PMF.uniformOfFintype OutputRowRest).bind (fun rest =>
      (PMF.uniformOfFintype PublicSample).bind (observe (outputSourceOracleRest rest))) =
    (PMF.uniformOfFintype (SourceOracleRest × PublicSample)).bind (fun source =>
      observe source.1 source.2) := by
  have mapped := congrArg (fun distribution => distribution.bind (fun coin =>
    observe (simulatorSourceEquiv.symm coin).1 (simulatorSourceEquiv.symm coin).2))
    map_uniform_simulatorSource
  simp only [PMF.bind_map, Function.comp_def, Equiv.symm_apply_apply] at mapped
  exact (bind_uniform_simulatorSource observe).trans mapped.symm

/-- This continuation uses only the selected curve target and the public oracle data. -/
def targetGateObserve [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField)
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      GarblingOracleData → PMF Observation)
    (selected : AffineInput × Aux) (source : SourceOracleRest × PublicSample) : PMF Observation :=
  (PMF.uniformOfFintype ((Fin 90 → Point) × (Fin outputMacCount → NonZeroBase))).bind fun online =>
    observe (publicMaskTable source.2) selected
      (source.2.curveRequest.retarget selected.1 source.1.1.1,
        (decodePoint selected.1).map fun point => retargetPointGateRequests source.2.pointRequests
          selected.1 (outputTargets (scalarMultiplication scalar point)
            (Vector.ofFn online.1) online.2)) source.1.2

/-- This source has the simulator's target key on both input branches. -/
def targetGateSourceRun [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField)
    (choose : Pipeline.Table → GarblingOracleData → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      GarblingOracleData → PMF Observation) : PMF Observation :=
  (PMF.uniformOfFintype (SourceOracleRest × PublicSample)).bind fun source =>
    (choose (publicMaskTable source.2) source.1.2).bind fun selected =>
      targetGateObserve scalar observe selected source

/-- The source key shift costs no probability when the observer does not read the old key. -/
theorem idealGateSourceRun_eq_targetGateSourceRun [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField)
    (choose : Pipeline.Table → GarblingOracleData → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      GarblingOracleData → PMF Observation) :
    idealGateSourceRun scalar (fun table rest => choose table rest.2)
      (fun table selected view rest => observe table selected view rest.2) =
        targetGateSourceRun scalar choose observe := by
  have joint := bind_uniform_outputSourceJoint (fun rest sample =>
    (choose (publicMaskTable sample) rest.2).bind fun selected =>
      targetGateObserve scalar observe selected (sourceSelectedCurveShift selected.1 (rest, sample)))
  have shifted := sourceSelectedCurveShift_run choose (targetGateObserve scalar observe)
  apply Eq.trans _ shifted
  simpa only [idealGateSourceRun, targetGateObserve, sourceSelectedCurveShift, retargetGateView,
    outputSourceOracleRest, Option.map_map, Function.comp_def, Equiv.coe_fn_mk] using joint

end

end Kriterion.ArgoMAC.Security
