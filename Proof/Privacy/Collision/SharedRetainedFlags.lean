import Proof.Privacy.Collision.SharedAdaptivePointBad
import Proof.Privacy.Collision.SharedReconstructedFreshness
import Proof.Privacy.Collision.RetainedSourceBadBound
import Proof.Privacy.Source.SharedSimulatorSourceDistribution

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype publicVectorFintype ciphertextFintype
  bitAdaptorTableFintype publicBitAdaptorKeyFintype
local instance retainedFlagsKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance retainedFlagsSampleNonempty : Nonempty PublicSample := ⟨defaultSimulatorCoin.tableSample⟩
local instance retainedFlagsVisibleNonempty : Nonempty VisiblePublicSample :=
  ⟨(PublicSample.visibleHiddenEquiv defaultSimulatorCoin.tableSample).1⟩
local instance retainedFlagsHiddenNonempty : Nonempty HiddenPublicSample :=
  ⟨(PublicSample.visibleHiddenEquiv defaultSimulatorCoin.tableSample).2⟩
local instance retainedFlagsOracleNonempty : Nonempty (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) :=
  ⟨(⟨fun _ => Equiv.refl Block⟩, ⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0))⟩

variable {Aux : Type*}
  (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
  (parameter : Nat) (auxiliary : Aux)

/-- The prefix uses the actual shared oracles before it samples the private input key. -/
def sharedRetainedCoinPrefix (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (bridge : BaseField) (sample : PublicSample) :=
  let state := Shared.Simulator.initialState (sample, defaultSimulatorCoin.inputKey, bridge) oracle
  runOracleProgramWithTranscript idealOracleHandler
    (adversary.chooseInput parameter state.table auxiliary) state.oracle

/-- Hidden targets leave the public prefix unchanged. -/
theorem sharedRetainedCoinPrefix_hidden (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (bridge : BaseField) (visible : VisiblePublicSample) (first second : HiddenPublicSample) :
    sharedRetainedCoinPrefix adversary parameter auxiliary oracle bridge
      (PublicSample.visibleHiddenEquiv.symm (visible, first)) =
    sharedRetainedCoinPrefix adversary parameter auxiliary oracle bridge
      (PublicSample.visibleHiddenEquiv.symm (visible, second)) := by
  unfold sharedRetainedCoinPrefix
  dsimp only
  rw [sharedInitialState_hidden_table visible first second]
  rfl

attribute [local irreducible] PMF.uniformOfFintype sharedRetainedCoinPrefix

/-- This pair records the point-row collision and the shared prequery collision. -/
def sharedRetainedFlagsAt (rows : Rows) (mask : BaseField)
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (bridge : BaseField) (sample : PublicSample) : PMF (Bool × Bool) :=
  (sharedRetainedCoinPrefix adversary parameter auxiliary oracle bridge sample).bind fun selected =>
    (PMF.uniformOfFintype InputMacKey).map fun key =>
      let source := (circuitMaskSampleSplit bridge mask rows selected.1.1 sample).2
      let history := sharedFixedTranscriptRecords selected.2.2
      (@decide (retainedSourceBirthday sample rows selected.1.1) (Classical.propDecidable _),
        @decide (sharedPrequeryLabelCollision history
          (sharedSourcePrequeryUses ⟨Shared.expandOracle oracle.1, oracle.2.1, oracle.2.2⟩ bridge source
            (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)) history) key)
          (Classical.propDecidable _))

/-- The complete flag distribution retains the three shared permutation slots. -/
def sharedRetainedFlags (rows : Rows) (mask : BaseField) : PMF (Bool × Bool) :=
  (PMF.uniformOfFintype (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind fun oracle =>
    (PMF.uniformOfFintype BaseField).bind fun bridge =>
      (PMF.uniformOfFintype PublicSample).bind (sharedRetainedFlagsAt adversary parameter auxiliary rows mask oracle bridge)

/-- The source prefix records at most the first-phase query budget. -/
theorem sharedRetainedCoinPrefix_length
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (bridge : BaseField) (sample : PublicSample) (selected)
    (member : selected ∈ (sharedRetainedCoinPrefix adversary parameter auxiliary oracle bridge sample).support) :
    (sharedFixedTranscriptRecords selected.2.2).length ≤ adversary.firstQueryBudget parameter := by
  unfold sharedRetainedCoinPrefix at member
  exact (sharedFixedTranscriptRecords_length _).trans
    (runOracleProgramWithTranscript_length_le _ _ _ _ member)

/-- The independent private key gives the exact shared prequery loss. -/
theorem sharedRetainedFlags_prequery [Fintype Block] (rows : Rows) (mask : BaseField) :
    (sharedRetainedFlags adversary parameter auxiliary rows mask).toOuterMeasure {flags | flags.2 = true} ≤
      (364 * adversary.firstQueryBudget parameter : Nat) / (2 : ENNReal) ^ 128 := by
  unfold sharedRetainedFlags sharedRetainedFlagsAt
  apply Probability.bind_event_le
  intro oracle _
  apply Probability.bind_event_le
  intro bridge _
  apply Probability.bind_event_le
  intro sample _
  apply Probability.bind_event_le
  intro selected member
  rw [PMF.toOuterMeasure_map_apply]
  simp only [Set.preimage_setOf_eq, decide_eq_true_eq]
  apply (sharedSourcePrequeryCollision_mass_le _ _ _ _ _).trans
  apply ENNReal.div_le_div_right
  exact_mod_cast Nat.mul_le_mul_left 364
    (sharedRetainedCoinPrefix_length adversary parameter auxiliary oracle bridge sample selected member)

/-- This flag records the point-row collision before the private key draw. -/
def sharedRetainedBirthday (rows : Rows) : PMF Bool :=
  (PMF.uniformOfFintype (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind fun oracle =>
    (PMF.uniformOfFintype BaseField).bind fun bridge =>
      (PMF.uniformOfFintype PublicSample).bind fun sample =>
        (sharedRetainedCoinPrefix adversary parameter auxiliary oracle bridge sample).map fun selected =>
          @decide (retainedSourceBirthday sample rows selected.1.1) (Classical.propDecidable _)

/-- Removing the key-dependent flag preserves the point-row flag exactly. -/
theorem sharedRetainedFlags_fst (rows : Rows) (mask : BaseField) :
    (sharedRetainedFlags adversary parameter auxiliary rows mask).map Prod.fst =
      sharedRetainedBirthday adversary parameter auxiliary rows := by
  simp only [sharedRetainedFlags, sharedRetainedFlagsAt, sharedRetainedBirthday,
    PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind, PMF.bind_const]

private theorem birthday_hidden (visible : VisiblePublicSample) (hidden : HiddenPublicSample)
    (rows : Rows) (input : AffineInput) :
    retainedSourceBirthday (PublicSample.visibleHiddenEquiv.symm (visible, hidden)) rows input =
      pointBranchCollision visible.2 (fun row => rows.get row) input
        (fun row => (evaluateRowsCubic rows input).get row) hidden.2 := by
  unfold retainedSourceBirthday
  have rowLaw (row : Fin outputMacCount) :
      (PublicSample.visibleHiddenEquiv.symm (visible, hidden)).points.get row =
        RowPublicSample.visibleHiddenEquiv.symm (visible.2 row, hidden.2 row) := Vector.get_ofFn _ _
  simp only [rowLaw, Equiv.apply_symm_apply]

/-- The visible prefix precedes the independent point targets. -/
theorem sharedRetainedBirthday_hidden (rows : Rows) :
    sharedRetainedBirthday adversary parameter auxiliary rows =
      (PMF.uniformOfFintype (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind fun oracle =>
        (PMF.uniformOfFintype BaseField).bind fun bridge =>
          (PMF.uniformOfFintype VisiblePublicSample).bind fun visible =>
            (sharedRetainedCoinPrefix adversary parameter auxiliary oracle bridge
              (PublicSample.visibleHiddenEquiv.symm (visible, Classical.arbitrary HiddenPublicSample))).bind fun selected =>
                (PMF.uniformOfFintype HiddenPublicSample).map fun hidden =>
                  @decide (pointBranchCollision visible.2 (fun row => rows.get row) selected.1.1
                    (fun row => (evaluateRowsCubic rows selected.1.1).get row) hidden.2) (Classical.propDecidable _) := by
  unfold sharedRetainedBirthday
  apply congrArg (PMF.uniformOfFintype (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind
  funext oracle
  apply congrArg (PMF.uniformOfFintype BaseField).bind
  funext bridge
  rw [sharedPublicSample_visible_hidden, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  apply congrArg (PMF.uniformOfFintype VisiblePublicSample).bind
  funext visible
  simp_rw [sharedRetainedCoinPrefix_hidden adversary parameter auxiliary oracle bridge visible _
    (Classical.arbitrary HiddenPublicSample)]
  simp only [PMF.map]
  rw [PMF.bind_comm]
  apply congrArg (sharedRetainedCoinPrefix adversary parameter auxiliary oracle bridge
    (PublicSample.visibleHiddenEquiv.symm (visible, Classical.arbitrary HiddenPublicSample))).bind
  funext selected
  apply congrArg (PMF.uniformOfFintype HiddenPublicSample).bind
  funext hidden
  dsimp only [Function.comp_def]
  rw [birthday_hidden visible hidden rows selected.1.1]

/-- The shared point-row flag has the checked birthday bound. -/
theorem sharedRetainedFlags_birthday [Fintype Block] (rows : Rows) (mask : BaseField) :
    (sharedRetainedFlags adversary parameter auxiliary rows mask).toOuterMeasure {flags | flags.1 = true} ≤
      (169786660680 / 1000) / (2 : ENNReal) ^ 128 := by
  have mass :
      (sharedRetainedBirthday adversary parameter auxiliary rows).toOuterMeasure {flag | flag = true} ≤
        (169786660680 / 1000) / (2 : ENNReal) ^ 128 := by
    rw [sharedRetainedBirthday_hidden]
    apply Probability.bind_event_le
    intro oracle _
    apply Probability.bind_event_le
    intro bridge _
    apply Probability.bind_event_le
    intro visible _
    apply Probability.bind_event_le
    intro selected _
    rw [PMF.toOuterMeasure_map_apply]
    simp only [Set.preimage_setOf_eq, decide_eq_true_eq]
    exact sharedPointBranchCollision_fullTape_mass_le visible.2 (fun row => rows.get row) selected.1.1
      (fun row => (evaluateRowsCubic rows selected.1.1).get row)
  rw [← sharedRetainedFlags_fst adversary parameter auxiliary rows mask, PMF.toOuterMeasure_map_apply] at mass
  exact mass

/-- The complete shared source pays one point-row loss and one prefix loss. -/
theorem sharedRetainedFlags_mass_le [Fintype Block] (rows : Rows) (mask : BaseField) :
    (sharedRetainedFlags adversary parameter auxiliary rows mask).toOuterMeasure
      {flags | flags.1 = true ∨ flags.2 = true} ≤
        (169786660680 / 1000) / (2 : ENNReal) ^ 128 +
          (364 * adversary.firstQueryBudget parameter : Nat) / (2 : ENNReal) ^ 128 :=
  (MeasureTheory.measure_union_le _ _).trans (add_le_add
    (sharedRetainedFlags_birthday adversary parameter auxiliary rows mask)
    (sharedRetainedFlags_prequery adversary parameter auxiliary rows mask))

end
end Kriterion.ArgoMAC.Security
