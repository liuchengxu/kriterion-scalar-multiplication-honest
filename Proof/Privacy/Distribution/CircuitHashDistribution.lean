import Proof.Privacy.Transcript.RealTranscriptMass
import Proof.Privacy.Distribution.CircuitMaskDistribution
import Proof.Privacy.Distribution.HashDistribution

namespace Kriterion.ArgoMAC.Security

open BN254

noncomputable section

attribute [local instance] bitAdaptorTableFintype publicVectorFintype circuitMaskSampleFintype

/-- This remainder keeps the field randomizers and public ciphertext tables. -/
abbrev MaskHashRest (randomizers adaptors : Nat) :=
  (Fin randomizers → BaseField) × (Fin adaptors → Vector BitAdaptor.Table coordinateBitCount)

abbrev RowHashRest := MaskHashRest 4 4 × MaskHashRest 3 3 × MaskHashRest 4 5
abbrev CircuitHashRest := MaskHashRest 2 5 × (Fin FieldMacToECMac.outputMacCount → RowHashRest)

local instance : Fintype RawCircuitGate := inferInstance
local instance : DecidableEq RawCircuitGate := Classical.decEq _

local instance (randomizers adaptors : Nat) : Fintype (MaskHashRest randomizers adaptors) := inferInstance
local instance : Fintype RowHashRest := inferInstance
local instance : Fintype CircuitHashRest := inferInstance

/-- This equivalence pairs each field mask with its complete-fiber quotient. -/
def maskHashSplitEquiv (randomizers adaptors : Nat) :
    (((Fin randomizers → BaseField) × (Fin adaptors → Fin coordinateBitCount → BaseField)) ×
      BiquadraticSampleRemainder adaptors) ≃
    (Fin adaptors → Fin coordinateBitCount → BaseField × HashLiftQuotient) ×
      MaskHashRest randomizers adaptors where
  toFun source := (fun adaptor bit => (source.1.2 adaptor bit, source.2.2 adaptor bit),
    source.1.1, source.2.1)
  invFun split := ((split.2.1, fun adaptor bit => (split.1 adaptor bit).1),
    split.2.2, fun adaptor bit => (split.1 adaptor bit).2)
  left_inv _ := rfl
  right_inv split := by
    apply Prod.ext
    · funext adaptor bit
      rfl
    · rfl

/-- This equivalence extracts the whole hash tape without discarding any source field. -/
def circuitMaskHashSplitEquiv :
    CircuitMaskSample ≃ (RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest where
  toFun source := (
    (fun gate => match gate with
      | .inl (adaptor, bit) => (maskHashSplitEquiv 2 5 source.1).1 adaptor bit
      | .inr (row, .inl (adaptor, bit)) =>
          (maskHashSplitEquiv 4 4 (source.2 row).1).1 adaptor bit
      | .inr (row, .inr (.inl (adaptor, bit))) =>
          (maskHashSplitEquiv 3 3 (source.2 row).2.1).1 adaptor bit
      | .inr (row, .inr (.inr (adaptor, bit))) =>
          (maskHashSplitEquiv 4 5 (source.2 row).2.2).1 adaptor bit),
    (maskHashSplitEquiv 2 5 source.1).2,
    fun row => ((maskHashSplitEquiv 4 4 (source.2 row).1).2,
      (maskHashSplitEquiv 3 3 (source.2 row).2.1).2,
      (maskHashSplitEquiv 4 5 (source.2 row).2.2).2))
  invFun split := (
    (maskHashSplitEquiv 2 5).symm
      ((fun adaptor bit => split.1 (.inl (adaptor, bit))), split.2.1),
    fun row => (
      (maskHashSplitEquiv 4 4).symm
        ((fun adaptor bit => split.1 (.inr (row, .inl (adaptor, bit)))), (split.2.2 row).1),
      (maskHashSplitEquiv 3 3).symm
        ((fun adaptor bit => split.1 (.inr (row, .inr (.inl (adaptor, bit))))), (split.2.2 row).2.1),
      (maskHashSplitEquiv 4 5).symm
        ((fun adaptor bit => split.1 (.inr (row, .inr (.inr (adaptor, bit))))), (split.2.2 row).2.2)))
  left_inv source := rfl
  right_inv split := by
    apply Prod.ext
    · funext gate
      rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
      · rfl
      · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;> rfl
    · rfl

local instance {count : Nat} : Nonempty (BiquadraticSampleRemainder count) :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable,
    fun _ _ => defaultHashLiftQuotient)⟩

local instance : Nonempty CircuitHashRest :=
  ⟨(circuitMaskHashSplitEquiv (Classical.choice (inferInstance : Nonempty CircuitMaskSample))).2⟩

/-- The actual circuit-mask sampler has independent uniform hash residues and quotients. -/
theorem map_uniform_circuitMaskHashSplit :
    (PMF.uniformOfFintype CircuitMaskSample).map circuitMaskHashSplitEquiv =
      PMF.uniformOfFintype ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest) :=
  map_uniformOfFintype_equivBetween circuitMaskHashSplitEquiv

/-- This source embeds every paired residue and quotient into its actual good hash lift. -/
def circuitGoodHashSource (source : CircuitMaskSample) :
    (RawCircuitGate → FullHashLift) × CircuitHashRest :=
  (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate),
    (circuitMaskHashSplitEquiv source).2)

/-- Whole-circuit rounding keeps every randomizer and ciphertext table in the observation. -/
theorem circuitHash_observation_bound {Observation : Type*}
    (observe : ((RawCircuitGate → FullHashLift) × CircuitHashRest) → PMF Observation)
    (event : Set Observation) :
    |(((PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)).bind
      observe).toOuterMeasure event).toReal -
      (((PMF.uniformOfFintype CircuitMaskSample).bind
        (observe ∘ circuitGoodHashSource)).toOuterMeasure event).toReal| ≤
      (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : ℕ) / 2 ^ 384 := by
  have source : (PMF.uniformOfFintype CircuitMaskSample).bind (observe ∘ circuitGoodHashSource) =
      (PMF.uniformOfFintype ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest)).bind
        (fun pair => observe ((fun gate => goodHashLiftSource (pair.1 gate)), pair.2)) := by
    rw [← map_uniform_circuitMaskHashSplit, PMF.bind_map]
    rfl
  rw [source]
  have bound := hashLift_family_product_observation_bound observe event
  have count : (Fintype.card RawCircuitGate : ℝ) = 278638 := by
    exact_mod_cast rawCircuitGate_card
  rwa [count] at bound

end

end Kriterion.ArgoMAC.Security
