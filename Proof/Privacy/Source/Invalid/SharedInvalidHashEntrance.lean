import Proof.Privacy.Source.Invalid.SharedInvalidHashGame
import Proof.Privacy.Source.Invalid.SharedInvalidRetainedSplit
import Proof.Privacy.Source.SharedGateSourceEntrance

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
noncomputable section
set_option maxRecDepth 4096
attribute [local instance 10] Classical.propDecidable
attribute [local instance] circuitMaskSampleFintype bitAdaptorTableFintype vectorFintype
  rowRandomnessFintype xRandomnessFintype yRandomnessFintype zRandomnessFintype
  instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1 instFintypeCircuitMaskTables
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1
local instance hashEntranceRemainder {count : Nat} : Nonempty (BiquadraticSampleRemainder count) :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable, fun _ _ => defaultHashLiftQuotient)⟩
attribute [local irreducible] PMF.uniformOfFintype circuitMaskSampleGarble

/-- This observation keeps the hidden bridge only for invalid inputs. -/
def sharedInvalidHashObserve {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (table : Pipeline.Table)
    (selected : AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))
    (view : SelectedGateView) (rest : SourceOracleRest) :
    PMF (Option (BaseField × SharedFullGateTranscript adversary.State)) :=
  if OnCurve selected.1 then PMF.pure none else
    (sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2).map
      (fun output => some (rest.1.1, output))

/-- The retained invalid observation runs exactly the shared curve branch. -/
theorem sharedInvalidHashRetained_mask [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (retained : SharedMaskRetainedTape) :
    ((PMF.uniformOfFintype CircuitMaskSample).bind fun source =>
      retainedGateSourceRun scalar retained.val source
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
        (sharedInvalidHashObserve adversary parameter auxiliary)) =
      sharedInvalidCurveMaskRun retained.val.2.2.1.1 retained.val.2.2.1.2.value
        (retainedSourceRows scalar retained.val) retained.val.2.2.2.inputMacKey
        (fun selected => selected.2.1)
        (fun table => sharedGateSourceChoose adversary parameter auxiliary table retained.val.2.2.2)
        (fun table selected bridge oracle =>
          (sharedCurveSourceSuffix adversary parameter auxiliary retained.val.2.2.2 table selected oracle).map
            (Prod.mk bridge)) := by
  unfold sharedInvalidCurveMaskRun
  apply congrArg (PMF.uniformOfFintype CircuitMaskSample).bind
  funext source
  unfold retainedGateSourceRun
  apply congrArg (sharedGateSourceChoose adversary parameter auxiliary _ _).bind
  funext selected
  by_cases valid : OnCurve selected.1
  · simp only [sharedInvalidHashObserve, sharedInvalidCurveObserve, if_pos valid]
  · have decoded : decodePoint selected.1 = none :=
      Classical.not_not.mp (fun nonzero => valid ((decodePoint_defined selected.1).mp nonzero))
    simp only [sharedInvalidHashObserve, sharedInvalidCurveObserve, if_neg valid,
      sharedGateSourceObserve, sharedCurveSourceSuffix, selectedGateView, decoded,
      Option.map_none, sharedProgramSelectedGateView, Shared.Simulator.program, PMF.map_comp,
      Function.comp_def, sourceInputLabels]

/-- The fixed-source split keeps the same row family for every bridge and mask. -/
theorem sharedCurveFixedSource_rows [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (source : SharedCurveFixedSource)
    (bridge : BaseField) (mask : NonZeroBase) :
    retainedSourceRows scalar (sharedCurveFixedSourceEquiv.symm (source, bridge, mask)).val =
      retainedSourceRows scalar (sharedCurveFixedSourceEquiv.symm (source, 0, ⟨1, one_ne_zero⟩)).val := rfl

local instance hashEntranceFixedNonempty [FieldCertificate] [GroupCertificate] : Nonempty SharedCurveFixedSource :=
  ⟨(sharedCurveFixedSourceEquiv (Classical.choice (inferInstance : Nonempty SharedMaskRetainedTape))).1⟩

/-- The independent retained source splits into the exact fixed-oracle invalid mask game. -/
theorem sharedInvalidHashRetained_split [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) :
    ((PMF.uniformOfFintype SharedMaskRetainedTape).bind fun retained =>
      (PMF.uniformOfFintype CircuitMaskSample).bind fun source =>
        retainedGateSourceRun scalar retained.val source
          (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
          (sharedInvalidHashObserve adversary parameter auxiliary)) =
    (PMF.uniformOfFintype SharedCurveFixedSource).bind fun source =>
      (PMF.uniformOfFintype BaseField).bind fun bridge =>
        (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
          sharedInvalidCurveMaskRun bridge mask.value
            (retainedSourceRows scalar (sharedCurveFixedSourceEquiv.symm (source, 0, ⟨1, one_ne_zero⟩)).val)
            source.val.2.2.inputMacKey (fun selected => selected.2.1)
            (fun table => sharedGateSourceChoose adversary parameter auxiliary table source.val.2.2)
            (fun table selected bridge oracle =>
              (sharedCurveSourceSuffix adversary parameter auxiliary source.val.2.2 table selected oracle).map
                (Prod.mk bridge)) := by
  rw [sharedCurveFixedSource_observation]
  simp_rw [sharedInvalidHashRetained_mask, sharedCurveFixedSource_rows]
  rfl

/-- The actual uniform shared retained source has the invalid bridge-query bound. -/
theorem sharedInvalidHashRetained_mass_le [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) :
    (((PMF.uniformOfFintype SharedMaskRetainedTape).bind fun retained =>
      (PMF.uniformOfFintype CircuitMaskSample).bind fun source =>
        retainedGateSourceRun scalar retained.val source
          (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
          (sharedInvalidHashObserve adversary parameter auxiliary)).toOuterMeasure
            (sharedInvalidHashEvent (fun output => output.2.2.1 ++ output.2.2.2.2.2))).toReal ≤
      ((adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter : Nat) + 1 : ℝ) / baseFieldModulus := by
  rw [sharedInvalidHashRetained_split]
  let bound : ℝ := ((adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter : Nat) + 1 : ℝ) / baseFieldModulus
  have nonnegative : 0 ≤ bound := by positivity
  have total := Probability.bind_event_le (PMF.uniformOfFintype SharedCurveFixedSource) _
    (sharedInvalidHashEvent (fun output : SharedFullGateTranscript adversary.State => output.2.2.1 ++ output.2.2.2.2.2))
    (ENNReal.ofReal bound) (fun source _ => by
      have localBound := sharedInvalidHashGame_mass_le adversary parameter auxiliary source.val.2.2
        (retainedSourceRows scalar (sharedCurveFixedSourceEquiv.symm (source, 0, ⟨1, one_ne_zero⟩)).val)
        (rowsForOutputKeysSparse _ _)
      apply (ENNReal.toReal_le_toReal (by
        rw [PMF.toOuterMeasure_apply]
        exact PMF.tsum_coe_indicator_ne_top _ _) ENNReal.ofReal_ne_top).mp
      rw [ENNReal.toReal_ofReal nonnegative]
      exact localBound)
  have result := ENNReal.toReal_mono ENNReal.ofReal_ne_top total
  rwa [ENNReal.toReal_ofReal nonnegative] at result

/-- The actual shared hash source has the exact independent retained invalid observation. -/
theorem sharedInvalidHashSource_retained [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness) :
    ((uniformRandomTape Shared.Randomness witness parameter).bind fun randomness =>
      (PMF.uniformOfFintype ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
        retainedGateSourceRun scalar (maskRetainedTape randomness.val)
          (sharedCircuitMaskSample randomness.val source.1 source.2)
          (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
          (sharedInvalidHashObserve adversary parameter auxiliary)) =
    (PMF.uniformOfFintype SharedMaskRetainedTape).bind fun retained =>
      (PMF.uniformOfFintype CircuitMaskSample).bind fun source =>
        retainedGateSourceRun scalar retained.val source
          (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
          (sharedInvalidHashObserve adversary parameter auxiliary) := by
  have split := actualSharedMaskSource_observation_eq witness parameter
    (fun retained source => retainedGateSourceRun scalar retained.val source
      (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
      (sharedInvalidHashObserve adversary parameter auxiliary))
  have marginal := congrArg (fun distribution => distribution.bind fun retained =>
    (PMF.uniformOfFintype CircuitMaskSample).bind fun source =>
      retainedGateSourceRun scalar retained.val source
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
        (sharedInvalidHashObserve adversary parameter auxiliary))
    (map_sharedRandomTape_maskRetained witness parameter)
  rw [PMF.bind_map] at marginal
  exact split.trans marginal

/-- This actual shared full source discards complete valid runs and incomplete tags. -/
def actualSharedInvalidHashSource [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness) :=
  actualSharedFullGateSource scalar witness parameter
    (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
    (sharedInvalidHashObserve adversary parameter auxiliary) (fun _ _ => PMF.pure none)

/-- The complete invalid shared source pays one hash-rounding loss and the exact hidden-bridge bound. -/
theorem actualSharedInvalidHashSource_mass_le [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness) :
    ((actualSharedInvalidHashSource adversary parameter auxiliary scalar witness).toOuterMeasure
      (sharedInvalidHashEvent (fun output => output.2.2.1 ++ output.2.2.2.2.2))).toReal ≤
      (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 +
      ((adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter : Nat) + 1 : ℝ) / baseFieldModulus := by
  have rounding := actualSharedFullGateSource_rounding_bound scalar witness parameter
    (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
    (sharedInvalidHashObserve adversary parameter auxiliary) (fun _ _ => PMF.pure none)
    (sharedInvalidHashEvent (fun output => output.2.2.1 ++ output.2.2.2.2.2))
  rw [sharedInvalidHashSource_retained] at rounding
  have hidden := sharedInvalidHashRetained_mass_le adversary parameter auxiliary scalar
  have difference := (abs_sub_le_iff.mp rounding).1
  unfold actualSharedInvalidHashSource
  linarith

end
end Kriterion.ArgoMAC.Security
