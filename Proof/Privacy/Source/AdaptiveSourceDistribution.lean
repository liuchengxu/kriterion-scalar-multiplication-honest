import Proof.Privacy.Distribution.MaskRandomizerDistribution
import Proof.Privacy.Distribution.AdaptiveOutputDistribution

namespace Kriterion.ArgoMAC.Security

open BN254 FieldMacToECMac

noncomputable section

attribute [local instance] vectorFintype rowRandomnessFintype xRandomnessFintype
  yRandomnessFintype zRandomnessFintype circuitMaskSampleFintype bitAdaptorTableFintype

attribute [local instance] instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
  instFintypeCircuitMaskTables instFintypeCircuitHashRest_1

local instance {count : Nat} : Nonempty (BiquadraticSampleRemainder count) :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable,
    fun _ _ => defaultHashLiftQuotient)⟩


/-- This view keeps the bridge key, curve mask, input key, and every actual oracle. -/
abbrev SourceOracleRest := (BaseField × NonZeroBase) × GarblingOracleData

/-- This projection removes only the obsolete field randomizers from the output rest. -/
def outputSourceOracleRest (rest : OutputRowRest) : SourceOracleRest :=
  ((rest.2.1.bridgeKey, rest.2.1.curveMask), rest.2.2)

private def sourceChoose {Aux : Type*}
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux)) :
    Pipeline.Table → OutputRowRest → PMF (AffineInput × Aux) :=
  fun table rest => choose table (outputSourceOracleRest rest)

private def sourceObserve {Aux Observation : Type*}
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      SourceOracleRest → PMF Observation) :
    Pipeline.Table → (AffineInput × Aux) → Option PublicSample → OutputRowRest → PMF Observation :=
  fun table selected sample rest => observe table selected sample (outputSourceOracleRest rest)

/-- This tape restores retained fields with zero obsolete randomizers. -/
def retainedSourceTape [FieldCertificate] [GroupCertificate]
    (retained : MaskRetainedTape) : Garbling.Randomness :=
  maskRandomizerTapeEquiv.symm (retained, (0, fun _ => (0, 0, 0)))

/-- This row family depends only on the retained offsets and scales. -/
def retainedSourceRows [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (retained : MaskRetainedTape) : Rows :=
  rowsForOutputKeys (outputKeys construction scalar (retainedSourceTape retained).offsets)
    (retainedSourceTape retained).pointRandomness

private theorem retainedSourceRows_actual [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (randomness : Garbling.Randomness) :
    retainedSourceRows scalar (maskRetainedTape randomness) =
      rowsForOutputKeys (outputKeys construction scalar randomness.offsets) randomness.pointRandomness := by
  apply maskRetainedTape_same_rows scalar
    (retainedSourceTape (maskRetainedTape randomness)) randomness
  change (maskRandomizerTapeEquiv (maskRandomizerTapeEquiv.symm
    (maskRetainedTape randomness, (0, fun _ => (0, 0, 0))))).1 = _
  rw [Equiv.apply_symm_apply]

/-- This run exposes the actual source table before the input choice. -/
def retainedSourceRun [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (retained : MaskRetainedTape) (source : CircuitMaskSample)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      SourceOracleRest → PMF Observation) : PMF Observation :=
  let rest := retained.2.2
  let rows := retainedSourceRows scalar retained
  let table := circuitMaskSourceTable rest.1.1 rest.1.2.value rows source
  (choose table rest).bind fun selected =>
    observe table selected ((decodePoint selected.1).map fun _ =>
      circuitMaskSampleGarble rest.1.1 rest.1.2.value rows selected.1 source) rest

private theorem retainedSourceRun_actual [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField) (randomness : Garbling.Randomness)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      SourceOracleRest → PMF Observation) :
    (PMF.uniformOfFintype CircuitMaskSample).bind (fun source =>
      retainedSourceRun scalar (maskRetainedTape randomness) source choose observe) =
    actualAdaptiveMaskRun scalar randomness
      (sourceChoose choose)
      (sourceObserve observe) := by
  unfold retainedSourceRun actualAdaptiveMaskRun
  rw [retainedSourceRows_actual]
  rfl


attribute [local instance] instNonemptyPublicSample_2

/-- This source uses the simulator's free points and scales after the adaptive input choice. -/
def idealSourceRun [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      SourceOracleRest → PMF Observation) : PMF Observation :=
  (PMF.uniformOfFintype OutputRowRest).bind fun rest =>
    (PMF.uniformOfFintype PublicSample).bind fun sample =>
      (choose (publicMaskTable sample) (outputSourceOracleRest rest)).bind fun selected =>
        (PMF.uniformOfFintype ((Fin 90 → Point) × (Fin outputMacCount → NonZeroBase))).bind fun coin =>
          observe (publicMaskTable sample) selected
            ((decodePoint selected.1).map fun point => sample.retargetMask selected.1 rest.2.1.bridgeKey
              (outputTargets (scalarMultiplication scalar point) (Vector.ofFn coin.1) coin.2))
            (outputSourceOracleRest rest)

private theorem idealSourceRun_output [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      SourceOracleRest → PMF Observation) :
    (PMF.uniformOfFintype OutputRowSource).bind (fun source =>
      (PMF.uniformOfFintype PublicSample).bind fun sample =>
        (sourceChoose choose (publicMaskTable sample) source.2.2).bind fun selected =>
          sourceObserve observe (publicMaskTable sample) selected
            (retargetOutput sample selected.1 (idealSelectedOutput scalar selected.1 source) source.2.2)
            source.2.2) = idealSourceRun scalar choose observe := by
  unfold sourceChoose sourceObserve
  rw [PMF.bind_comm]
  unfold idealSourceRun
  conv_rhs => rw [PMF.bind_comm]
  apply congrArg ((PMF.uniformOfFintype PublicSample).bind)
  funext sample
  have law := idealOutput_encodingSource scalar
    (fun rest => choose (publicMaskTable sample) (outputSourceOracleRest rest))
    (fun selected result rest => observe (publicMaskTable sample) selected
      (retargetOutput sample selected.1 result rest) (outputSourceOracleRest rest))
  simpa only [retargetOutput, Option.map_map, Function.comp_def] using law

private theorem sourceObservation_transport {Observation : Type*}
    {first second first' second' : PMF Observation} {event : Set Observation} {error : ℝ}
    (firstLaw : first = first') (secondLaw : second = second')
    (bound : |(first'.toOuterMeasure event).toReal - (second'.toOuterMeasure event).toReal| ≤ error) :
    |(first.toOuterMeasure event).toReal - (second.toOuterMeasure event).toReal| ≤ error := by
  rw [firstLaw, secondLaw]
  exact bound

private theorem retainedSource_observation_eq [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      SourceOracleRest → PMF Observation) :
    (randomTape witness parameter).bind (fun randomness =>
      (PMF.uniformOfFintype
        ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
          retainedSourceRun scalar (maskRetainedTape randomness)
            (sharedCircuitMaskSample randomness source.1 source.2) choose observe) =
    (randomTape witness parameter).bind (fun randomness => actualAdaptiveMaskRun scalar randomness
      (sourceChoose choose)
      (sourceObserve observe)) := by
  exact (sharedMaskSource_observation_eq witness parameter
    (fun retained source => retainedSourceRun scalar retained source choose observe)).trans
    (congrArg ((randomTape witness parameter).bind)
      (funext fun randomness => retainedSourceRun_actual scalar randomness choose observe))

/-- The exact shared source reaches the ideal encoding source with only the offset loss. -/
theorem sharedSource_ideal_observation_bound [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      SourceOracleRest → PMF Observation) (event : Set Observation) :
    |((idealSourceRun scalar choose observe).toOuterMeasure event).toReal -
      (((randomTape witness parameter).bind (fun randomness =>
        (PMF.uniformOfFintype
          ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
            retainedSourceRun scalar (maskRetainedTape randomness)
              (sharedCircuitMaskSample randomness source.1 source.2) choose observe)).toOuterMeasure
                event).toReal| ≤ (2 : ℝ) ^ (-240 : ℤ) := by
  exact sourceObservation_transport (Observation := Observation) (event := event)
    (error := (2 : ℝ) ^ (-240 : ℤ))
    (idealSourceRun_output scalar choose observe).symm
    (retainedSource_observation_eq scalar witness parameter choose observe)
    (adaptiveMaskOutput_observation_bound scalar witness parameter
      (sourceChoose choose)
      (sourceObserve observe) event)

/-- This decoder reads the residue and quotient on complete hash fibers. -/
def fullSourceHashPair (lift : FullHashLift) : BaseField × HashLiftQuotient :=
  match hashLiftSplitEquiv lift with
  | .inl good => goodHashLiftEquiv good
  | .inr _ => (0, defaultHashLiftQuotient)

theorem fullSourceHashPair_good (pair : BaseField × HashLiftQuotient) :
    fullSourceHashPair (goodHashLiftSource pair) = pair := by
  unfold fullSourceHashPair goodHashLiftSource
  rw [hashLiftSplitEquiv.apply_symm_apply]
  exact goodHashLiftEquiv.apply_symm_apply pair

/-- This condition says that every full hash value belongs to a complete field fiber. -/
def FullSourceComplete (hash : RawCircuitGate → FullHashLift) : Prop :=
  ∀ gate, ∃ pair, goodHashLiftSource pair = hash gate

/-- This source uses every original field randomizer and ciphertext table. -/
def decodeFullSource (source : (RawCircuitGate → FullHashLift) × CircuitHashRest) : CircuitMaskSample :=
  circuitMaskHashSplitEquiv.symm ((fun gate => fullSourceHashPair (source.1 gate)), source.2)

private theorem decodeFullSource_good (source : CircuitMaskSample) :
    decodeFullSource (circuitGoodHashSource source) = source := by
  simp only [decodeFullSource, circuitGoodHashSource, fullSourceHashPair_good]
  exact circuitMaskHashSplitEquiv.symm_apply_apply source

/-- This run keeps full hashes and uses an explicit fallback outside complete fibers. -/
def fullSourceRun [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (retained : MaskRetainedTape)
    (source : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation) :
    PMF Observation := by
  classical
  exact if FullSourceComplete source.1 then
    retainedSourceRun scalar retained (decodeFullSource source) choose observe
  else fallback retained source

private theorem fullSourceRun_good [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField) (retained : MaskRetainedTape)
    (source : CircuitMaskSample)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation) :
    fullSourceRun scalar retained (circuitGoodHashSource source) choose observe fallback =
      retainedSourceRun scalar retained source choose observe := by
  have complete : FullSourceComplete (circuitGoodHashSource source).1 :=
    fun gate => ⟨(circuitMaskHashSplitEquiv source).1 gate, rfl⟩
  simp only [fullSourceRun, if_pos complete, decodeFullSource_good]

private theorem fullSourceRun_good_pair [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField) (retained : MaskRetainedTape)
    (pair : (RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation) :
    fullSourceRun scalar retained ((fun gate => goodHashLiftSource (pair.1 gate)), pair.2)
      choose observe fallback =
      retainedSourceRun scalar retained (circuitMaskHashSplitEquiv.symm pair) choose observe := by
  have complete : FullSourceComplete (fun gate => goodHashLiftSource (pair.1 gate)) :=
    fun gate => ⟨pair.1 gate, rfl⟩
  simp only [fullSourceRun, if_pos complete, decodeFullSource, fullSourceHashPair_good]

attribute [local instance] instNonemptyCircuitHashRest_1

/-- This distribution keeps the full actual hash source and shared field randomizers. -/
def fullAdaptiveSource [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation) :
    PMF Observation :=
  (randomTape witness parameter).bind fun randomness =>
    (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitMaskTables)).bind fun source =>
      fullSourceRun scalar (maskRetainedTape randomness)
        (source.1, sharedCircuitHashRest randomness source.2) choose observe fallback

private def fullSourceKernel [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (source : (RawCircuitGate → FullHashLift) × CircuitHashRest) : PMF Observation :=
  (PMF.uniformOfFintype MaskRetainedTape).bind fun retained =>
    fullSourceRun scalar retained source choose observe fallback

private def goodSourceKernel [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      SourceOracleRest → PMF Observation)
    (source : (RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest) : PMF Observation :=
  (PMF.uniformOfFintype MaskRetainedTape).bind fun retained =>
    retainedSourceRun scalar retained (circuitMaskHashSplitEquiv.symm source) choose observe

private theorem fullSourceKernel_good [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (source : (RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest) :
    fullSourceKernel scalar choose observe fallback ((fun gate => goodHashLiftSource (source.1 gate)), source.2) =
      goodSourceKernel scalar choose observe source := by
  unfold fullSourceKernel goodSourceKernel
  apply congrArg ((PMF.uniformOfFintype MaskRetainedTape).bind)
  funext retained
  exact fullSourceRun_good_pair scalar retained source choose observe fallback

private theorem fullAdaptiveSource_rounding_bound [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (event : Set Observation) :
    |((fullAdaptiveSource scalar witness parameter choose observe fallback).toOuterMeasure event).toReal -
      (((randomTape witness parameter).bind (fun randomness =>
        (PMF.uniformOfFintype
          ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
            retainedSourceRun scalar (maskRetainedTape randomness)
              (sharedCircuitMaskSample randomness source.1 source.2) choose observe)).toOuterMeasure
                event).toReal| ≤ (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : ℕ) / 2 ^ 384 := by
  have full := sharedHashSource_observation_eq witness parameter
    (fun retained source => fullSourceRun scalar retained source choose observe fallback)
  change fullAdaptiveSource scalar witness parameter choose observe fallback =
    (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)).bind
      (fullSourceKernel scalar choose observe fallback) at full
  have good := sharedHashSource_observation_eq witness parameter
    (fun retained source => retainedSourceRun scalar retained
      (circuitMaskHashSplitEquiv.symm source) choose observe)
  change (randomTape witness parameter).bind (fun randomness =>
      (PMF.uniformOfFintype
        ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
          retainedSourceRun scalar (maskRetainedTape randomness)
            (sharedCircuitMaskSample randomness source.1 source.2) choose observe) =
    (PMF.uniformOfFintype ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest)).bind
      (fun pair => goodSourceKernel scalar choose observe pair) at good
  have bound := hashLift_family_product_observation_bound
    (fullSourceKernel scalar choose observe fallback) event
  have mapped := congrArg
    ((PMF.uniformOfFintype ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest)).bind)
    (funext fun pair => fullSourceKernel_good scalar choose observe fallback pair)
  have count : (Fintype.card RawCircuitGate : ℝ) = 278638 := by
    exact_mod_cast rawCircuitGate_card
  rw [count] at bound
  exact sourceObservation_transport (Observation := Observation) (event := event)
    (error := (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : ℕ) / 2 ^ 384) full (good.trans mapped.symm) bound

/-- The full source reaches the ideal output source before the final transcript comparison. -/
theorem adaptiveSource_observation_bound [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (event : Set Observation) :
    |((fullAdaptiveSource scalar witness parameter choose observe fallback).toOuterMeasure event).toReal -
      ((idealSourceRun scalar choose observe).toOuterMeasure event).toReal| ≤
      (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : ℕ) / 2 ^ 384 + (2 : ℝ) ^ (-240 : ℤ) := by
  have rounding := fullAdaptiveSource_rounding_bound scalar witness parameter choose observe fallback event
  have output := sharedSource_ideal_observation_bound scalar witness parameter choose observe event
  have triangle := abs_sub_le
    ((fullAdaptiveSource scalar witness parameter choose observe fallback).toOuterMeasure event).toReal
    ((((randomTape witness parameter).bind (fun randomness =>
      (PMF.uniformOfFintype
        ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
          retainedSourceRun scalar (maskRetainedTape randomness)
            (sharedCircuitMaskSample randomness source.1 source.2) choose observe)).toOuterMeasure event).toReal)
    ((idealSourceRun scalar choose observe).toOuterMeasure event).toReal
  rw [abs_sub_comm ((idealSourceRun scalar choose observe).toOuterMeasure event).toReal] at output
  exact triangle.trans (add_le_add rounding output)

end

end Kriterion.ArgoMAC.Security
