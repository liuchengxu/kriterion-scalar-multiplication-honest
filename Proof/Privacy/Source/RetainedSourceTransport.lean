import Proof.Privacy.Simulator.SimulatorSourceDistribution

namespace Kriterion.ArgoMAC.Security

open BN254 FieldMacToECMac
noncomputable section

attribute [local instance] bitAdaptorTableFintype publicVectorFintype ciphertextFintype
  xMaskSampleFintype yMaskSampleFintype zMaskSampleFintype curveMaskSampleFintype
  rowMaskSampleFintype circuitMaskSampleFintype instNonemptyPublicSample_2
  instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1 instFintypeCircuitMaskTables

local instance {count : Nat} : Nonempty (BiquadraticSampleRemainder count) :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable,
    fun _ _ => defaultHashLiftQuotient)⟩

/-- This change of variables keeps the full source prescription after the input choice. -/
theorem adaptiveRetainedSource_observation_eq {Aux Observation : Type*}
    (key mask : BaseField) (rows : Rows)
    (sparse : ∀ index, SparseRow (rows.get index))
    (choose : Pipeline.Table → PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → CircuitMaskSample → PMF Observation) :
    (PMF.uniformOfFintype CircuitMaskSample).bind (fun source =>
      (choose (circuitMaskSourceTable key mask rows source)).bind fun selected =>
        observe selected source) =
    (PMF.uniformOfFintype PublicSample).bind (fun sample =>
      (choose (publicMaskTable sample)).bind fun selected =>
        observe selected (circuitMaskSampleSplit key mask rows selected.1 sample).2) := by
  have law := congrArg (fun distribution => distribution.bind
    (fun pair : (AffineInput × Aux) × CircuitMaskSample => observe pair.1 pair.2))
    (adaptiveCircuitMaskSplit_uniform key mask rows sparse choose)
  simp only [PMF.bind_bind, PMF.bind_map] at law
  exact law.symm

attribute [local instance] instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

private def retainedHashKernel [FieldCertificate] [GroupCertificate] {Observation : Type*}
    (observe : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (source : (RawCircuitGate → FullHashLift) × CircuitHashRest) : PMF Observation :=
  (PMF.uniformOfFintype MaskRetainedTape).bind fun retained => observe retained source

private theorem retainedObservation_transport {Observation : Type*}
    {first second first' second' : PMF Observation} {event : Set Observation} {error : ℝ}
    (firstEq : first = first') (secondEq : second = second')
    (bound : |(first'.toOuterMeasure event).toReal - (second'.toOuterMeasure event).toReal| ≤ error) :
    |(first.toOuterMeasure event).toReal - (second.toOuterMeasure event).toReal| ≤ error := by
  rw [firstEq, secondEq]
  exact bound

/-- This observer embeds each complete field fiber into its full hash value. -/
def retainedGoodHashObserver [FieldCertificate] [GroupCertificate] {Observation : Type*}
    (observe : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (retained : MaskRetainedTape)
    (source : (RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest) : PMF Observation :=
  observe retained ((fun gate => goodHashLiftSource (source.1 gate)), source.2)

/-- Full hash rounding permits any observer of the retained source prescription. -/
theorem sharedRetainedHash_observation_bound [FieldCertificate] [GroupCertificate]
    {Observation : Type*} (witness : Garbling.Randomness) (parameter : Nat)
    (observe : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (event : Set Observation) :
    |(((randomTape witness parameter).bind (fun randomness =>
        (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitMaskTables)).bind fun source =>
          observe (maskRetainedTape randomness)
            (source.1, sharedCircuitHashRest randomness source.2))).toOuterMeasure event).toReal -
      (((randomTape witness parameter).bind (fun randomness =>
        (PMF.uniformOfFintype
          ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
            retainedGoodHashObserver observe (maskRetainedTape randomness)
              (source.1, sharedCircuitHashRest randomness source.2))).toOuterMeasure event).toReal| ≤
      (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : ℕ) / 2 ^ 384 := by
  have full := sharedHashSource_observation_eq witness parameter observe
  have good := sharedHashSource_observation_eq witness parameter
    (retainedGoodHashObserver observe)
  change _ = (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)).bind
    (retainedHashKernel observe) at full
  change _ = (PMF.uniformOfFintype
    ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest)).bind
      (fun source => retainedHashKernel observe ((fun gate => goodHashLiftSource (source.1 gate)), source.2)) at good
  have bound := hashLift_family_product_observation_bound (retainedHashKernel observe) event
  have count : (Fintype.card RawCircuitGate : ℝ) = 278638 := by exact_mod_cast rawCircuitGate_card
  rw [count] at bound
  exact retainedObservation_transport (Observation := Observation) (event := event)
    (error := (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : ℕ) / 2 ^ 384) full good bound

/-- These coins determine the retained row coefficients and curve mask. -/
abbrev RetainedRowCoin [FieldCertificate] [GroupCertificate] :=
  ClampedAffineOffsets × (Fin outputMacCount → NonZeroBase) × NonZeroBase

/-- This split separates the actual retained rows and mask from the simulator coin. -/
def retainedSimulatorSourceEquiv [FieldCertificate] [GroupCertificate] :
    (MaskRetainedTape × PublicSample) ≃ RetainedRowCoin × SimulatorCoin where
  toFun source :=
    ((source.1.1, source.1.2.1, source.1.2.2.1.2),
      (simulatorSourceEquiv (source.1.2.2, source.2)).1)
  invFun source :=
    ((source.1.1, source.1.2.1, (simulatorSourceEquiv.symm (source.2, source.1.2.2)).1),
      source.2.tableSample)
  left_inv source := by
    rcases source with ⟨⟨offsets, rhos, ⟨bridge, mask⟩, ⟨fixed, key, enc, hash⟩⟩, sample⟩
    rfl
  right_inv source := by
    rcases source with ⟨⟨offsets, rhos, mask⟩, ⟨sample, ⟨fixed, enc, hash⟩, key, bridge⟩⟩
    rfl

local instance [FieldCertificate] [GroupCertificate] : Nonempty (RetainedRowCoin × SimulatorCoin) :=
  Nonempty.map retainedSimulatorSourceEquiv inferInstance

/-- The retained row coins and simulator coin are exactly independent. -/
theorem map_uniform_retainedSimulatorSource [FieldCertificate] [GroupCertificate] :
    (PMF.uniformOfFintype (MaskRetainedTape × PublicSample)).map retainedSimulatorSourceEquiv =
      PMF.uniformOfFintype (RetainedRowCoin × SimulatorCoin) :=
  map_uniformOfFintype_equivBetween retainedSimulatorSourceEquiv

end
end Kriterion.ArgoMAC.Security
