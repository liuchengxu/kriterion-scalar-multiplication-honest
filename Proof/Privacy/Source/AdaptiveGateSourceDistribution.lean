import Proof.Privacy.Source.AdaptiveSourceDistribution

namespace Kriterion.ArgoMAC.Security

open BN254 FieldMacToECMac

noncomputable section

attribute [local instance] vectorFintype rowRandomnessFintype xRandomnessFintype
  yRandomnessFintype zRandomnessFintype circuitMaskSampleFintype
  instNonemptyPublicSample_2

local instance {count : Nat} : Nonempty (BiquadraticSampleRemainder count) :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable,
    fun _ _ => defaultHashLiftQuotient)⟩

/-- This view keeps the curve source for every input. -/
abbrev SelectedGateView := CurveGateRequest × Option PointGateRequests

/-- This projection removes only the unused point requests on invalid inputs. -/
def selectedGateView [FieldCertificate] (sample : PublicSample) (input : AffineInput) : SelectedGateView :=
  (sample.curveRequest, (decodePoint input).map fun _ => sample.pointRequests)

/-- This operation changes the output rows and keeps the complete curve request. -/
def retargetGateView (sample : PublicSample) (input : AffineInput)
    (result : Option Result) (rest : OutputRowRest) : SelectedGateView :=
  (sample.curveRequest.retarget input
    (rest.2.1.bridgeKey + rest.2.1.curveMask.value * (input.x ^ 3 + 3 - input.y ^ 2)),
    result.map fun value => retargetPointGateRequests sample.pointRequests input value.pointMacs)

private theorem selectedGateView_actualOutput [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (randomness : Garbling.Randomness)
    (input : AffineInput) (sample : PublicSample) :
    selectedGateView (sample.retargetMask input
      (randomness.bridgeKey + randomness.curveMask.value * (input.x ^ 3 + 3 - input.y ^ 2))
      (evaluateRowsCubic (rowsForOutputKeys (outputKeys construction scalar randomness.offsets)
        randomness.pointRandomness) input)) input =
    retargetGateView sample input (actualSelectedOutput scalar input randomness)
      (actualOutputRest randomness) := by
  simp only [selectedGateView, retargetGateView, actualSelectedOutput,
    PublicSample.retargetMask_curveRequest, PublicSample.retargetMask_pointRequests]
  cases decoded : decodePoint input with
  | none => rfl
  | some point =>
      have onCurve : OnCurve input := (decodePoint_defined input).mp (by rw [decoded]; simp)
      rw [evaluateRowsCubic_eq _ (rowsForOutputKeysSparse _ _) input onCurve]
      rfl

/-- This mask run exposes the curve request on invalid inputs. -/
def actualAdaptiveGateMaskRun [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (randomness : Garbling.Randomness)
    (choose : Pipeline.Table → OutputRowRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      OutputRowRest → PMF Observation) : PMF Observation :=
  let rows := rowsForOutputKeys (outputKeys construction scalar randomness.offsets)
    randomness.pointRandomness
  (PMF.uniformOfFintype CircuitMaskSample).bind fun source =>
    let table := circuitMaskSourceTable randomness.bridgeKey randomness.curveMask.value rows source
    (choose table (actualOutputRest randomness)).bind fun selected =>
      observe table selected
        (selectedGateView
          (circuitMaskSampleGarble randomness.bridgeKey randomness.curveMask.value rows selected.1 source)
          selected.1) (actualOutputRest randomness)

/-- The adaptive mask change preserves the selected curve request on both branches. -/
theorem actualAdaptiveGateMaskRun_retarget [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField) (randomness : Garbling.Randomness)
    (choose : Pipeline.Table → OutputRowRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      OutputRowRest → PMF Observation) :
    actualAdaptiveGateMaskRun scalar randomness choose observe =
    (PMF.uniformOfFintype PublicSample).bind (fun sample =>
      (choose (publicMaskTable sample) (actualOutputRest randomness)).bind fun selected =>
        observe (publicMaskTable sample) selected
          (retargetGateView sample selected.1 (actualSelectedOutput scalar selected.1 randomness)
            (actualOutputRest randomness)) (actualOutputRest randomness)) := by
  let rows := rowsForOutputKeys (outputKeys construction scalar randomness.offsets)
    randomness.pointRandomness
  have same := congrArg (fun distribution => distribution.bind
    (fun pair : (AffineInput × Aux) × PublicSample =>
      observe (publicMaskTable pair.2) pair.1 (selectedGateView pair.2 pair.1.1)
        (actualOutputRest randomness)))
    (adaptiveCircuitMaskGarble_eq_retarget randomness.bridgeKey randomness.curveMask.value rows
      (rowsForOutputKeysSparse _ _) (fun table => choose table (actualOutputRest randomness)))
  have table (input : AffineInput) (source : CircuitMaskSample) :
      publicMaskTable (circuitMaskSampleGarble randomness.bridgeKey
        randomness.curveMask.value rows input source) =
      circuitMaskSourceTable randomness.bridgeKey randomness.curveMask.value rows source :=
    circuitMaskSampleGarble_table_input _ _ _ _ input ⟨0, 0⟩
  simp only [PMF.bind_bind, PMF.bind_map] at same
  dsimp only [Function.comp_def] at same
  simp only [table, publicMaskTable_retarget] at same
  simpa only [rows, selectedGateView_actualOutput, actualAdaptiveGateMaskRun] using same

private theorem gate_bind_tagged {Input Sample Aux Output Observation : Type*}
    (samples : PMF Sample) (choose : Sample → PMF (Input × Aux))
    (output : Input → Output) (observe : Sample → (Input × Aux) → Output → PMF Observation) :
    (samples.bind (fun sample => (choose sample).map fun selected =>
      (selected.1, sample, selected.2))).bind (fun selected =>
        observe selected.2.1 (selected.1, selected.2.2) (output selected.1)) =
    samples.bind (fun sample => (choose sample).bind fun selected =>
      observe sample selected (output selected.1)) := by
  rw [PMF.bind_bind]
  apply congrArg samples.bind
  funext sample
  rw [PMF.bind_map]
  rfl

/-- The output-row bound retains the curve source when the selected point is invalid. -/
theorem adaptiveGateMaskOutput_observation_bound [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → OutputRowRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      OutputRowRest → PMF Observation) (event : Set Observation) :
    |(((PMF.uniformOfFintype OutputRowSource).bind (fun source =>
        (PMF.uniformOfFintype PublicSample).bind (fun sample =>
          (choose (publicMaskTable sample) source.2.2).bind fun selected =>
            observe (publicMaskTable sample) selected
              (retargetGateView sample selected.1 (idealSelectedOutput scalar selected.1 source)
                source.2.2) source.2.2))).toOuterMeasure event).toReal -
      (((randomTape witness parameter).bind (fun randomness =>
        actualAdaptiveGateMaskRun scalar randomness choose observe)).toOuterMeasure event).toReal| ≤
      (2 : ℝ) ^ (-240 : ℤ) := by
  simp_rw [actualAdaptiveGateMaskRun_retarget]
  have bound := adaptiveOutput_observation_bound scalar witness parameter
    (fun rest => (PMF.uniformOfFintype PublicSample).bind (fun sample =>
      (choose (publicMaskTable sample) rest).map fun selected =>
        (selected.1, sample, selected.2)))
    (fun selected result rest => observe (publicMaskTable selected.2.1)
      (selected.1, selected.2.2) (retargetGateView selected.2.1 selected.1 result rest) rest) event
  have idealTagged (source : OutputRowSource) := gate_bind_tagged
    (PMF.uniformOfFintype PublicSample) (fun sample => choose (publicMaskTable sample) source.2.2)
    (fun input => idealSelectedOutput scalar input source)
    (fun sample selected result => observe (publicMaskTable sample) selected
      (retargetGateView sample selected.1 result source.2.2) source.2.2)
  have actualTagged (randomness : Garbling.Randomness) := gate_bind_tagged
    (PMF.uniformOfFintype PublicSample)
    (fun sample => choose (publicMaskTable sample) (actualOutputRest randomness))
    (fun input => actualSelectedOutput scalar input randomness)
    (fun sample selected result => observe (publicMaskTable sample) selected
      (retargetGateView sample selected.1 result (actualOutputRest randomness))
        (actualOutputRest randomness))
  simp only [idealTagged, actualTagged] at bound
  exact bound


attribute [local instance] bitAdaptorTableFintype instFintypeRawCircuitGate_1
  instDecidableEqRawCircuitGate_1 instFintypeCircuitMaskTables instFintypeCircuitHashRest_1
  instNonemptyCircuitHashRest_1

private def gateSourceChoose {Aux : Type*}
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux)) :
    Pipeline.Table → OutputRowRest → PMF (AffineInput × Aux) :=
  fun table rest => choose table (outputSourceOracleRest rest)

private def gateSourceObserve {Aux Observation : Type*}
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation) :
    Pipeline.Table → (AffineInput × Aux) → SelectedGateView → OutputRowRest → PMF Observation :=
  fun table selected view rest => observe table selected view (outputSourceOracleRest rest)

/-- This projected run keeps all curve gates after the input choice. -/
def retainedGateSourceRun [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (retained : MaskRetainedTape) (source : CircuitMaskSample)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation) : PMF Observation :=
  let rest := retained.2.2
  let rows := retainedSourceRows scalar retained
  let table := circuitMaskSourceTable rest.1.1 rest.1.2.value rows source
  (choose table rest).bind fun selected =>
    observe table selected (selectedGateView
      (circuitMaskSampleGarble rest.1.1 rest.1.2.value rows selected.1 source) selected.1) rest

private theorem gateSourceRows_actual [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (randomness : Garbling.Randomness) :
    retainedSourceRows scalar (maskRetainedTape randomness) =
      rowsForOutputKeys (outputKeys construction scalar randomness.offsets) randomness.pointRandomness := by
  apply maskRetainedTape_same_rows scalar
    (retainedSourceTape (maskRetainedTape randomness)) randomness
  change (maskRandomizerTapeEquiv (maskRandomizerTapeEquiv.symm
    (maskRetainedTape randomness, (0, fun _ => (0, 0, 0))))).1 = _
  rw [Equiv.apply_symm_apply]

private theorem retainedGateSourceRun_actual [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField) (randomness : Garbling.Randomness)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation) :
    (PMF.uniformOfFintype CircuitMaskSample).bind (fun source =>
      retainedGateSourceRun scalar (maskRetainedTape randomness) source choose observe) =
    actualAdaptiveGateMaskRun scalar randomness (gateSourceChoose choose) (gateSourceObserve observe) := by
  unfold retainedGateSourceRun actualAdaptiveGateMaskRun
  rw [gateSourceRows_actual scalar]
  rfl

/-- This source keeps the curve request and uses the simulator's online point coin. -/
def idealGateSourceRun [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation) : PMF Observation :=
  (PMF.uniformOfFintype OutputRowRest).bind fun rest =>
    (PMF.uniformOfFintype PublicSample).bind fun sample =>
      (choose (publicMaskTable sample) (outputSourceOracleRest rest)).bind fun selected =>
        (PMF.uniformOfFintype ((Fin 90 → Point) × (Fin outputMacCount → NonZeroBase))).bind fun coin =>
          observe (publicMaskTable sample) selected
            (retargetGateView sample selected.1 ((decodePoint selected.1).map fun point =>
              ⟨selected.1, outputTargets (scalarMultiplication scalar point) (Vector.ofFn coin.1) coin.2⟩) rest)
            (outputSourceOracleRest rest)

private theorem idealGateSourceRun_output [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation) :
    (PMF.uniformOfFintype OutputRowSource).bind (fun source =>
      (PMF.uniformOfFintype PublicSample).bind fun sample =>
        (gateSourceChoose choose (publicMaskTable sample) source.2.2).bind fun selected =>
          gateSourceObserve observe (publicMaskTable sample) selected
            (retargetGateView sample selected.1 (idealSelectedOutput scalar selected.1 source) source.2.2)
            source.2.2) = idealGateSourceRun scalar choose observe := by
  unfold gateSourceChoose gateSourceObserve
  rw [PMF.bind_comm]
  unfold idealGateSourceRun
  conv_rhs => rw [PMF.bind_comm]
  apply congrArg ((PMF.uniformOfFintype PublicSample).bind)
  funext sample
  exact idealOutput_encodingSource scalar
    (fun rest => choose (publicMaskTable sample) (outputSourceOracleRest rest))
    (fun selected result rest => observe (publicMaskTable sample) selected
      (retargetGateView sample selected.1 result rest) (outputSourceOracleRest rest))

private theorem gateObservation_transport {Observation : Type*}
    {first second first' second' : PMF Observation} {event : Set Observation} {error : ℝ}
    (firstLaw : first = first') (secondLaw : second = second')
    (bound : |(first'.toOuterMeasure event).toReal - (second'.toOuterMeasure event).toReal| ≤ error) :
    |(first.toOuterMeasure event).toReal - (second.toOuterMeasure event).toReal| ≤ error := by
  rw [firstLaw, secondLaw]
  exact bound

private theorem retainedGateSource_observation_eq [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation) :
    (randomTape witness parameter).bind (fun randomness =>
      (PMF.uniformOfFintype
        ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
          retainedGateSourceRun scalar (maskRetainedTape randomness)
            (sharedCircuitMaskSample randomness source.1 source.2) choose observe) =
    (randomTape witness parameter).bind (fun randomness => actualAdaptiveGateMaskRun scalar randomness
      (gateSourceChoose choose) (gateSourceObserve observe)) := by
  exact (sharedMaskSource_observation_eq witness parameter
    (fun retained source => retainedGateSourceRun scalar retained source choose observe)).trans
    (congrArg ((randomTape witness parameter).bind)
      (funext fun randomness => retainedGateSourceRun_actual scalar randomness choose observe))

/-- The shared source retains invalid curve gates while it replaces valid point outputs. -/
theorem sharedGateSource_ideal_observation_bound [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation) (event : Set Observation) :
    |((idealGateSourceRun scalar choose observe).toOuterMeasure event).toReal -
      (((randomTape witness parameter).bind (fun randomness =>
        (PMF.uniformOfFintype
          ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
            retainedGateSourceRun scalar (maskRetainedTape randomness)
              (sharedCircuitMaskSample randomness source.1 source.2) choose observe)).toOuterMeasure
                event).toReal| ≤ (2 : ℝ) ^ (-240 : ℤ) := by
  exact gateObservation_transport (Observation := Observation) (event := event)
    (error := (2 : ℝ) ^ (-240 : ℤ))
    (idealGateSourceRun_output scalar choose observe).symm
    (retainedGateSource_observation_eq scalar witness parameter choose observe)
    (adaptiveGateMaskOutput_observation_bound scalar witness parameter
      (gateSourceChoose choose) (gateSourceObserve observe) event)


/-- This run keeps full hashes and uses an explicit fallback outside complete fibers. -/
def fullGateSourceRun [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (retained : MaskRetainedTape)
    (source : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation) :
    PMF Observation := by
  classical
  exact if FullSourceComplete source.1 then
    retainedGateSourceRun scalar retained (decodeFullSource source) choose observe
  else fallback retained source

private theorem fullGateSourceRun_good_pair [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField) (retained : MaskRetainedTape)
    (pair : (RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation) :
    fullGateSourceRun scalar retained ((fun gate => goodHashLiftSource (pair.1 gate)), pair.2)
      choose observe fallback =
      retainedGateSourceRun scalar retained (circuitMaskHashSplitEquiv.symm pair) choose observe := by
  have complete : FullSourceComplete (fun gate => goodHashLiftSource (pair.1 gate)) :=
    fun gate => ⟨pair.1 gate, rfl⟩
  rw [fullGateSourceRun, if_pos complete]
  simp only [decodeFullSource, fullSourceHashPair_good]

attribute [local instance] instNonemptyCircuitHashRest_1

/-- This distribution keeps the full actual hash source and shared field randomizers. -/
def fullAdaptiveGateSource [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation) :
    PMF Observation :=
  (randomTape witness parameter).bind fun randomness =>
    (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitMaskTables)).bind fun source =>
      fullGateSourceRun scalar (maskRetainedTape randomness)
        (source.1, sharedCircuitHashRest randomness source.2) choose observe fallback

private def fullGateSourceKernel [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (source : (RawCircuitGate → FullHashLift) × CircuitHashRest) : PMF Observation :=
  (PMF.uniformOfFintype MaskRetainedTape).bind fun retained =>
    fullGateSourceRun scalar retained source choose observe fallback

private def goodGateSourceKernel [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation)
    (source : (RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest) : PMF Observation :=
  (PMF.uniformOfFintype MaskRetainedTape).bind fun retained =>
    retainedGateSourceRun scalar retained (circuitMaskHashSplitEquiv.symm source) choose observe

private theorem fullGateSourceKernel_good [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (source : (RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest) :
    fullGateSourceKernel scalar choose observe fallback ((fun gate => goodHashLiftSource (source.1 gate)), source.2) =
      goodGateSourceKernel scalar choose observe source := by
  unfold fullGateSourceKernel goodGateSourceKernel
  apply congrArg ((PMF.uniformOfFintype MaskRetainedTape).bind)
  funext retained
  exact fullGateSourceRun_good_pair scalar retained source choose observe fallback

private theorem fullAdaptiveGateSource_rounding_bound [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (event : Set Observation) :
    |((fullAdaptiveGateSource scalar witness parameter choose observe fallback).toOuterMeasure event).toReal -
      (((randomTape witness parameter).bind (fun randomness =>
        (PMF.uniformOfFintype
          ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
            retainedGateSourceRun scalar (maskRetainedTape randomness)
              (sharedCircuitMaskSample randomness source.1 source.2) choose observe)).toOuterMeasure
                event).toReal| ≤ (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : ℕ) / 2 ^ 384 := by
  have full := sharedHashSource_observation_eq witness parameter
    (fun retained source => fullGateSourceRun scalar retained source choose observe fallback)
  change fullAdaptiveGateSource scalar witness parameter choose observe fallback =
    (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)).bind
      (fullGateSourceKernel scalar choose observe fallback) at full
  have good := sharedHashSource_observation_eq witness parameter
    (fun retained source => retainedGateSourceRun scalar retained
      (circuitMaskHashSplitEquiv.symm source) choose observe)
  change (randomTape witness parameter).bind (fun randomness =>
      (PMF.uniformOfFintype
        ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
          retainedGateSourceRun scalar (maskRetainedTape randomness)
            (sharedCircuitMaskSample randomness source.1 source.2) choose observe) =
    (PMF.uniformOfFintype ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest)).bind
      (fun pair => goodGateSourceKernel scalar choose observe pair) at good
  have bound := hashLift_family_product_observation_bound
    (fullGateSourceKernel scalar choose observe fallback) event
  have mapped := congrArg
    ((PMF.uniformOfFintype ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest)).bind)
    (funext fun pair => fullGateSourceKernel_good scalar choose observe fallback pair)
  have count : (Fintype.card RawCircuitGate : ℝ) = 278638 := by
    exact_mod_cast rawCircuitGate_card
  rw [count] at bound
  exact gateObservation_transport (Observation := Observation) (event := event)
    (error := (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : ℕ) / 2 ^ 384) full (good.trans mapped.symm) bound

/-- The full source reaches the ideal output source before the final transcript comparison. -/
theorem adaptiveGateSource_observation_bound [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (event : Set Observation) :
    |((fullAdaptiveGateSource scalar witness parameter choose observe fallback).toOuterMeasure event).toReal -
      ((idealGateSourceRun scalar choose observe).toOuterMeasure event).toReal| ≤
      (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : ℕ) / 2 ^ 384 + (2 : ℝ) ^ (-240 : ℤ) := by
  have rounding := fullAdaptiveGateSource_rounding_bound scalar witness parameter choose observe fallback event
  have output := sharedGateSource_ideal_observation_bound scalar witness parameter choose observe event
  have triangle := abs_sub_le
    ((fullAdaptiveGateSource scalar witness parameter choose observe fallback).toOuterMeasure event).toReal
    ((((randomTape witness parameter).bind (fun randomness =>
      (PMF.uniformOfFintype
        ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
          retainedGateSourceRun scalar (maskRetainedTape randomness)
            (sharedCircuitMaskSample randomness source.1 source.2) choose observe)).toOuterMeasure event).toReal)
    ((idealGateSourceRun scalar choose observe).toOuterMeasure event).toReal
  rw [abs_sub_comm ((idealGateSourceRun scalar choose observe).toOuterMeasure event).toReal] at output
  exact triangle.trans (add_le_add rounding output)

end

end Kriterion.ArgoMAC.Security
