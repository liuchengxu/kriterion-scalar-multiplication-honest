/- This file connects ideal collision events to the actual adaptive prefix. -/

import Proof.Privacy.Transcript.AdaptiveTranscript
import Proof.Privacy.Collision.ActiveCollision
import Proof.Privacy.Distribution.GateProgrammingDistribution
import Proof.Privacy.Distribution.CircuitMaskDistribution
import Proof.Privacy.Bounds.AdaptiveArithmetic

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

/-- The pre-encode oracle program does not read hidden table targets. -/
theorem runCircuitSimulatorWithTranscript
    {Result : Type*} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget)
    (state : CircuitSimulatorState) :
    runOracleProgramWithTranscript circuitSimulatorOracleHandler program state =
      (runOracleProgramWithTranscript idealOracleHandler program state.oracle).map
        (fun output => (output.1, {state with oracle := output.2.1}, output.2.2)) := by
  induction program generalizing state with
  | pure result =>
      simp only [runOracleProgramWithTranscript_pure, PMF.map_comp]
      rfl
  | query request next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript_query, circuitSimulatorOracleHandler]
      rw [inductionHypothesis, PMF.map_comp, PMF.map_comp]
      rfl
  | sample distribution next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript_sample, PMF.map_bind]
      congr 1
      funext value
      exact inductionHypothesis value state

/-- These fields determine the public coefficient and ciphertext rows. -/
abbrev VisibleGateSample (coefficients gates : Nat) :=
  (Fin coefficients → BaseField) × (Fin gates → Vector BitAdaptor.Table coordinateBitCount)

/-- These hidden fields determine the simulator targets and their hash lifts. -/
abbrev HiddenGateSample (gates : Nat) :=
  (Fin gates → Fin coordinateBitCount → BaseField) ×
    (Fin gates → Fin coordinateBitCount → HashLiftQuotient)

def CurvePublicSample.visibleHiddenEquiv :
    CurvePublicSample ≃ VisibleGateSample 3 5 × HiddenGateSample 5 where
  toFun sample := ((sample.coefficients, sample.tables), (sample.targets, sample.quotients))
  invFun pair := {
    coefficients := pair.1.1
    tables := pair.1.2
    targets := pair.2.1
    quotients := pair.2.2 }
  left_inv sample := by cases sample; rfl
  right_inv _ := rfl

def XPublicSample.visibleHiddenEquiv :
    XPublicSample ≃ VisibleGateSample 5 4 × HiddenGateSample 4 where
  toFun sample := ((sample.coefficients, sample.tables), (sample.targets, sample.quotients))
  invFun pair := {
    coefficients := pair.1.1
    tables := pair.1.2
    targets := pair.2.1
    quotients := pair.2.2 }
  left_inv sample := by cases sample; rfl
  right_inv _ := rfl

def YPublicSample.visibleHiddenEquiv :
    YPublicSample ≃ VisibleGateSample 4 3 × HiddenGateSample 3 where
  toFun sample := ((sample.coefficients, sample.tables), (sample.targets, sample.quotients))
  invFun pair := {
    coefficients := pair.1.1
    tables := pair.1.2
    targets := pair.2.1
    quotients := pair.2.2 }
  left_inv sample := by cases sample; rfl
  right_inv _ := rfl

def ZPublicSample.visibleHiddenEquiv :
    ZPublicSample ≃ VisibleGateSample 5 5 × HiddenGateSample 5 where
  toFun sample := ((sample.coefficients, sample.tables), (sample.targets, sample.quotients))
  invFun pair := {
    coefficients := pair.1.1
    tables := pair.1.2
    targets := pair.2.1
    quotients := pair.2.2 }
  left_inv sample := by cases sample; rfl
  right_inv _ := rfl

abbrev VisibleRowSample :=
  VisibleGateSample 5 4 × VisibleGateSample 4 3 × VisibleGateSample 5 5

abbrev HiddenRowSample := HiddenGateSample 4 × HiddenGateSample 3 × HiddenGateSample 5

def RowPublicSample.visibleHiddenEquiv :
    RowPublicSample ≃ VisibleRowSample × HiddenRowSample where
  toFun sample :=
    (((XPublicSample.visibleHiddenEquiv sample.x).1,
      (YPublicSample.visibleHiddenEquiv sample.y).1,
      (ZPublicSample.visibleHiddenEquiv sample.z).1),
    ((XPublicSample.visibleHiddenEquiv sample.x).2,
      (YPublicSample.visibleHiddenEquiv sample.y).2,
      (ZPublicSample.visibleHiddenEquiv sample.z).2))
  invFun pair := {
    x := XPublicSample.visibleHiddenEquiv.symm (pair.1.1, pair.2.1)
    y := YPublicSample.visibleHiddenEquiv.symm (pair.1.2.1, pair.2.2.1)
    z := ZPublicSample.visibleHiddenEquiv.symm (pair.1.2.2, pair.2.2.2) }
  left_inv sample := by cases sample; rfl
  right_inv _ := rfl

abbrev VisiblePublicSample :=
  VisibleGateSample 3 5 × (Fin FieldMacToECMac.outputMacCount → VisibleRowSample)

abbrev HiddenPublicSample :=
  HiddenGateSample 5 × (Fin FieldMacToECMac.outputMacCount → HiddenRowSample)

/-- This equivalence keeps every inactive target in the hidden component. -/
def PublicSample.visibleHiddenEquiv :
    PublicSample ≃ VisiblePublicSample × HiddenPublicSample where
  toFun sample :=
    (((CurvePublicSample.visibleHiddenEquiv sample.curve).1,
      fun row => (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).1),
    ((CurvePublicSample.visibleHiddenEquiv sample.curve).2,
      fun row => (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).2))
  invFun pair := {
    curve := CurvePublicSample.visibleHiddenEquiv.symm (pair.1.1, pair.2.1)
    points := Vector.ofFn fun row =>
      RowPublicSample.visibleHiddenEquiv.symm (pair.1.2 row, pair.2.2 row) }
  left_inv sample := by
    cases sample with
    | mk curve points =>
      change PublicSample.mk curve (Vector.ofFn fun row => points.get row) =
        PublicSample.mk curve points
      exact congrArg (PublicSample.mk curve) (vectorFunctionEquiv.right_inv points)
  right_inv pair := by
    rcases pair with ⟨⟨curveVisible, rowsVisible⟩, curveHidden, rowsHidden⟩
    simp only [Vector.get_ofFn]
    rfl

abbrev VisibleSimulatorCoin :=
  VisiblePublicSample × SimulatorOracleCoin × InputMacKey × BaseField

private def simulatorCoinFieldsEquiv :
    SimulatorCoin ≃ PublicSample × SimulatorOracleCoin × InputMacKey × BaseField where
  toFun coin := (coin.tableSample, coin.oracles, coin.inputKey, coin.bridgeKey)
  invFun pair := {
    tableSample := pair.1
    oracles := pair.2.1
    inputKey := pair.2.2.1
    bridgeKey := pair.2.2.2 }
  left_inv coin := by cases coin; rfl
  right_inv _ := rfl

/-- This split places every public-prefix input before the hidden target tape. -/
def SimulatorCoin.visibleHiddenEquiv :
    SimulatorCoin ≃ VisibleSimulatorCoin × HiddenPublicSample :=
  simulatorCoinFieldsEquiv.trans
    ((PublicSample.visibleHiddenEquiv.prodCongr (Equiv.refl _)).trans {
      toFun := fun pair => ((pair.1.1, pair.2), pair.1.2)
      invFun := fun pair => ((pair.1.1, pair.2), pair.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })

attribute [local instance] publicVectorFintype ciphertextFintype bitAdaptorTableFintype
  publicBitAdaptorKeyFintype publicInputMacKeyFintype

local instance (gates : Nat) : Fintype (HiddenGateSample gates) := inferInstance
local instance : Fintype HiddenRowSample := inferInstance

local instance : Nonempty SimulatorCoin := ⟨defaultSimulatorCoin⟩
local instance : Nonempty VisibleSimulatorCoin :=
  ⟨(SimulatorCoin.visibleHiddenEquiv defaultSimulatorCoin).1⟩
local instance : Nonempty HiddenPublicSample :=
  ⟨(SimulatorCoin.visibleHiddenEquiv defaultSimulatorCoin).2⟩

/-- The offline coin gives independent uniform visible and hidden components. -/
theorem simulatorCoin_visibleHidden_uniform :
    (PMF.uniformOfFintype SimulatorCoin).map SimulatorCoin.visibleHiddenEquiv =
      PMF.uniformOfFintype (VisibleSimulatorCoin × HiddenPublicSample) :=
  map_uniformOfFintype_equivBetween SimulatorCoin.visibleHiddenEquiv

theorem uniform_simulatorCoin_split :
    PMF.uniformOfFintype SimulatorCoin =
      (PMF.uniformOfFintype VisibleSimulatorCoin).bind fun visible =>
        (PMF.uniformOfFintype HiddenPublicSample).map fun hidden =>
          SimulatorCoin.visibleHiddenEquiv.symm (visible, hidden) := by
  calc
    _ = (PMF.uniformOfFintype (VisibleSimulatorCoin × HiddenPublicSample)).map
        SimulatorCoin.visibleHiddenEquiv.symm :=
      (map_uniformOfFintype_equivBetween SimulatorCoin.visibleHiddenEquiv.symm).symm
    _ = (PMF.uniformOfFintype HiddenPublicSample).bind fun hidden =>
        (PMF.uniformOfFintype VisibleSimulatorCoin).map fun visible =>
          SimulatorCoin.visibleHiddenEquiv.symm (visible, hidden) := by
      rw [uniform_prod_eq_bind, PMF.map_bind]
      simp only [PMF.map_comp, Function.comp_def]
    _ = _ := by
      simp only [PMF.map, Function.comp_def]
      exact PMF.bind_comm _ _ _

private theorem publicSample_hidden_rowTable (visible : VisiblePublicSample)
    (first second : HiddenPublicSample) (row : Fin FieldMacToECMac.outputMacCount) :
    ((PublicSample.visibleHiddenEquiv.symm (visible, first)).pointRequests.get row).table =
      ((PublicSample.visibleHiddenEquiv.symm (visible, second)).pointRequests.get row).table := by
  simp only [PublicSample.pointRequests, Vector.get_map]
  change (RowPublicSample.request ((Vector.ofFn fun index =>
      RowPublicSample.visibleHiddenEquiv.symm (visible.2 index, first.2 index)).get row)).table =
    (RowPublicSample.request ((Vector.ofFn fun index =>
      RowPublicSample.visibleHiddenEquiv.symm (visible.2 index, second.2 index)).get row)).table
  rw [Vector.get_ofFn, Vector.get_ofFn]
  rfl

private theorem publicSample_hidden_pointTable (visible : VisiblePublicSample)
    (first second : HiddenPublicSample) :
    pointGateTable (PublicSample.visibleHiddenEquiv.symm (visible, first)).pointRequests =
      pointGateTable (PublicSample.visibleHiddenEquiv.symm (visible, second)).pointRequests := by
  have rows := publicSample_hidden_rowTable visible first second
  have x := congrArg Vector.ofFn (funext fun row =>
    congrArg FieldMacToECMac.RowTable.x (rows row))
  have y := congrArg Vector.ofFn (funext fun row =>
    congrArg FieldMacToECMac.RowTable.y (rows row))
  have z := congrArg Vector.ofFn (funext fun row =>
    congrArg FieldMacToECMac.RowTable.z (rows row))
  unfold pointGateTable
  rw [x, y, z]

/-- Hidden gate targets do not change the actual public table. -/
theorem simulatorCoin_hidden_table (visible : VisibleSimulatorCoin)
    (first second : HiddenPublicSample) :
    (SimulatorCoin.visibleHiddenEquiv.symm (visible, first)).state.table =
      (SimulatorCoin.visibleHiddenEquiv.symm (visible, second)).state.table := by
  apply congrArg₂ Pipeline.Table.mk
  · rfl
  · exact publicSample_hidden_pointTable visible.1 first second

/-- Hidden gate targets do not change the initial oracle state. -/
theorem simulatorCoin_hidden_oracle (visible : VisibleSimulatorCoin)
    (first second : HiddenPublicSample) :
    (SimulatorCoin.visibleHiddenEquiv.symm (visible, first)).state.oracle =
      (SimulatorCoin.visibleHiddenEquiv.symm (visible, second)).state.oracle := rfl

private def swapNestedSeed {Rows Positions : Type*} [DecidableEq Rows]
    [DecidableEq Positions] (row : Rows) (position : Positions) :
    ((Rows → Positions → BaseField) × BaseField) ≃
      ((Rows → Positions → BaseField) × BaseField) :=
  (show Function.Involutive (fun sample : (Rows → Positions → BaseField) × BaseField =>
    (Function.update sample.1 row (Function.update (sample.1 row) position sample.2),
      sample.1 row position)) by
    intro sample
    simp only [Function.update_self, Function.update_idem]
    simp).toPerm _

/-- A nonzero low-seed coefficient gives an exact uniform target marginal. -/
theorem uniform_affine_nestedCoordinate
    {Rows Positions : Type*} [Fintype Rows] [Fintype Positions]
    [DecidableEq Rows] [DecidableEq Positions] (row : Rows) (position : Positions)
    (target : (Rows → Positions → BaseField) → BaseField)
    (shift : ∀ values seed,
      target (Function.update values row (Function.update (values row) position seed)) =
        target values + values row position - seed) :
    (PMF.uniformOfFintype (Rows → Positions → BaseField)).map target =
      PMF.uniformOfFintype BaseField := by
  have law := congrArg (fun distribution => distribution.map (target ∘ Prod.fst))
    (map_uniformOfFintype_equivBetween (swapNestedSeed row position))
  rw [PMF.map_comp] at law
  have right : (PMF.uniformOfFintype ((Rows → Positions → BaseField) × BaseField)).map
      (target ∘ Prod.fst) =
        (PMF.uniformOfFintype (Rows → Positions → BaseField)).map target := by
    rw [← PMF.map_comp, map_uniform_prod_fst]
  rw [right] at law
  rw [← law, uniform_prod_eq_bind, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, swapNestedSeed,
    Function.Involutive.coe_toPerm]
  simp_rw [shift]
  simp only [PMF.map, Function.comp_def]
  rw [PMF.bind_comm]
  change ((PMF.uniformOfFintype (Rows → Positions → BaseField)).bind fun values =>
    (PMF.uniformOfFintype BaseField).map
      (fun seed => target values + values row position - seed)) = _
  simp_rw [uniform_subtract_field]
  exact PMF.bind_const _ _

/-- A seed coefficient that is a unit gives the same exact uniform target marginal.
Pre-scaling the target by the inverse reduces this to the coefficient-one law. -/
theorem uniform_affine_nestedCoordinate_scaled
    {Rows Positions : Type*} [Fintype Rows] [Fintype Positions]
    [DecidableEq Rows] [DecidableEq Positions] (row : Rows) (position : Positions)
    (scale inverse : BaseField) (cancel : inverse * scale = 1)
    (target : (Rows → Positions → BaseField) → BaseField)
    (shift : ∀ values seed,
      target (Function.update values row (Function.update (values row) position seed)) =
        target values + scale * values row position - scale * seed) :
    (PMF.uniformOfFintype (Rows → Positions → BaseField)).map target =
      PMF.uniformOfFintype BaseField := by
  have scaled : (PMF.uniformOfFintype (Rows → Positions → BaseField)).map
      (fun values => inverse * target values) = PMF.uniformOfFintype BaseField := by
    apply uniform_affine_nestedCoordinate row position
    intro values seed
    rw [shift, show inverse * (target values + scale * values row position - scale * seed) =
      inverse * target values + inverse * scale * values row position -
        inverse * scale * seed from by ring, cancel, one_mul, one_mul]
  have restored : (fun values : Rows → Positions → BaseField =>
      scale * (inverse * target values)) = target := by
    funext values
    rw [show scale * (inverse * target values) = scale * inverse * target values from by ring,
      mul_comm scale inverse, cancel, one_mul]
  have back := congrArg (fun distribution : PMF BaseField =>
    distribution.map (fun value => scale * value)) scaled
  simp only [PMF.map_comp, Function.comp_def] at back
  rw [restored] at back
  rw [back, uniform_scale_field scale inverse cancel]

local instance collisionCoordinateNeZero : NeZero coordinateBitCount := ⟨by decide⟩

/-- The full uniform target tape gives a uniform actual pivot. -/
theorem XPublicSample.pivot_uniform_targets (sample : XPublicSample)
    (input : AffineInput) (target : BaseField) :
    (PMF.uniformOfFintype (Fin 4 → Fin coordinateBitCount → BaseField)).map
      (fun values => (({sample with targets := values} : XPublicSample).request.retarget
        input target).x9Targets 0) = PMF.uniformOfFintype BaseField := by
  apply uniform_affine_nestedCoordinate 2 0
  intro values seed
  exact XPublicSample.pivot_seed ({sample with targets := values} : XPublicSample)
    input target seed

/-- The full uniform target tape gives a uniform actual pivot. -/
theorem YPublicSample.pivot_uniform_targets (sample : YPublicSample)
    (input : AffineInput) (target : BaseField) :
    (PMF.uniformOfFintype (Fin 3 → Fin coordinateBitCount → BaseField)).map
      (fun values => (({sample with targets := values} : YPublicSample).request.retarget
        input target).x9Targets 0) = PMF.uniformOfFintype BaseField := by
  apply uniform_affine_nestedCoordinate_scaled 2 1 2 twoInverse twoInverse_cancel
  intro values seed
  exact YPublicSample.pivot_seed ({sample with targets := values} : YPublicSample)
    input target seed

/-- The full uniform target tape gives a uniform actual pivot. -/
theorem ZPublicSample.pivot_uniform_targets (sample : ZPublicSample)
    (input : AffineInput) (target : BaseField) :
    (PMF.uniformOfFintype (Fin 5 → Fin coordinateBitCount → BaseField)).map
      (fun values => (({sample with targets := values} : ZPublicSample).request.retarget
        input target).x9Targets 0) = PMF.uniformOfFintype BaseField := by
  apply uniform_affine_nestedCoordinate 2 0
  intro values seed
  exact ZPublicSample.pivot_seed ({sample with targets := values} : ZPublicSample)
    input target seed

/-- The full uniform target tape gives a uniform actual pivot. -/
theorem CurvePublicSample.pivot_uniform_targets (sample : CurvePublicSample)
    (input : AffineInput) (target : BaseField) :
    (PMF.uniformOfFintype (Fin 5 → Fin coordinateBitCount → BaseField)).map
      (fun values => (({sample with targets := values} : CurvePublicSample).request.retarget
        input target).x7Targets 0) = PMF.uniformOfFintype BaseField := by
  apply uniform_affine_nestedCoordinate 4 0
  intro values seed
  exact CurvePublicSample.pivot_seed ({sample with targets := values} : CurvePublicSample)
    input target seed

private theorem uniform_function_eval {Index Value : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Value] [Nonempty Value] (index : Index) :
    (PMF.uniformOfFintype (Index → Value)).map (fun values => values index) =
      PMF.uniformOfFintype Value := by
  have law := congrArg (fun distribution => distribution.map Prod.fst)
    (map_uniformOfFintype_equivBetween (Equiv.piSplitAt index (fun _ => Value)))
  simpa only [PMF.map_comp, map_uniform_prod_fst, Function.comp_def, Equiv.piSplitAt_apply] using law

private theorem uniform_nested_eval {Rows Positions : Type*}
    [Fintype Rows] [Fintype Positions] [DecidableEq Rows] [DecidableEq Positions]
    (row : Rows) (position : Positions) :
    (PMF.uniformOfFintype (Rows → Positions → BaseField)).map
      (fun values => values row position) = PMF.uniformOfFintype BaseField := by
  have law := congrArg (fun distribution => distribution.map (fun values => values position))
    (uniform_function_eval (Value := Positions → BaseField) row)
  rw [PMF.map_comp, uniform_function_eval] at law
  exact law

private theorem retargetBits_free {count : Nat} (values : Fin (count + 1) → BaseField)
    (target : BaseField) (position : Fin (count + 1)) (nonzero : position ≠ 0) :
    retargetBits values target position = values position := by
  rcases (Fin.eq_zero_or_eq_succ position).resolve_left nonzero with ⟨index, rfl⟩
  rfl

/-- Every actual retargeted coordinate has a uniform field marginal. -/
theorem XPublicSample.target_uniform (sample : XPublicSample)
    (input : AffineInput) (target : BaseField)
    (gate : Fin 4) (position : Fin coordinateBitCount) :
    (PMF.uniformOfFintype (Fin 4 → Fin coordinateBitCount → BaseField)).map
      (fun values => (({sample with targets := values} : XPublicSample).retargetMask
        input target).targets gate position) = PMF.uniformOfFintype BaseField := by
  by_cases pivot : gate = 3 ∧ position = 0
  · rcases pivot with ⟨rfl, rfl⟩
    exact XPublicSample.pivot_uniform_targets sample input target
  · have unchanged : ∀ values,
        (({sample with targets := values} : XPublicSample).retargetMask input target).targets
          gate position = values gate position := by
      intro values
      simp only [XPublicSample.retargetMask]
      by_cases same : gate = 3
      · subst gate
        rw [Function.update_self]
        exact retargetBits_free _ _ position (by simpa using pivot)
      · rw [Function.update_of_ne same]
    simp_rw [unchanged]
    exact uniform_nested_eval gate position

/-- Every actual retargeted coordinate has a uniform field marginal. -/
theorem YPublicSample.target_uniform (sample : YPublicSample)
    (input : AffineInput) (target : BaseField)
    (gate : Fin 3) (position : Fin coordinateBitCount) :
    (PMF.uniformOfFintype (Fin 3 → Fin coordinateBitCount → BaseField)).map
      (fun values => (({sample with targets := values} : YPublicSample).retargetMask
        input target).targets gate position) = PMF.uniformOfFintype BaseField := by
  by_cases pivot : gate = 2 ∧ position = 0
  · rcases pivot with ⟨rfl, rfl⟩
    exact YPublicSample.pivot_uniform_targets sample input target
  · have unchanged : ∀ values,
        (({sample with targets := values} : YPublicSample).retargetMask input target).targets
          gate position = values gate position := by
      intro values
      simp only [YPublicSample.retargetMask]
      by_cases same : gate = 2
      · subst gate
        rw [Function.update_self]
        exact retargetBits_free _ _ position (by simpa using pivot)
      · rw [Function.update_of_ne same]
    simp_rw [unchanged]
    exact uniform_nested_eval gate position

/-- Every actual retargeted coordinate has a uniform field marginal. -/
theorem ZPublicSample.target_uniform (sample : ZPublicSample)
    (input : AffineInput) (target : BaseField)
    (gate : Fin 5) (position : Fin coordinateBitCount) :
    (PMF.uniformOfFintype (Fin 5 → Fin coordinateBitCount → BaseField)).map
      (fun values => (({sample with targets := values} : ZPublicSample).retargetMask
        input target).targets gate position) = PMF.uniformOfFintype BaseField := by
  by_cases pivot : gate = 4 ∧ position = 0
  · rcases pivot with ⟨rfl, rfl⟩
    exact ZPublicSample.pivot_uniform_targets sample input target
  · have unchanged : ∀ values,
        (({sample with targets := values} : ZPublicSample).retargetMask input target).targets
          gate position = values gate position := by
      intro values
      simp only [ZPublicSample.retargetMask]
      by_cases same : gate = 4
      · subst gate
        rw [Function.update_self]
        exact retargetBits_free _ _ position (by simpa using pivot)
      · rw [Function.update_of_ne same]
    simp_rw [unchanged]
    exact uniform_nested_eval gate position

/-- Every actual retargeted coordinate has a uniform field marginal. -/
theorem CurvePublicSample.target_uniform (sample : CurvePublicSample)
    (input : AffineInput) (target : BaseField)
    (gate : Fin 5) (position : Fin coordinateBitCount) :
    (PMF.uniformOfFintype (Fin 5 → Fin coordinateBitCount → BaseField)).map
      (fun values => (({sample with targets := values} : CurvePublicSample).retargetMask
        input target).targets gate position) = PMF.uniformOfFintype BaseField := by
  by_cases pivot : gate = 2 ∧ position = 0
  · rcases pivot with ⟨rfl, rfl⟩
    exact CurvePublicSample.pivot_uniform_targets sample input target
  · have unchanged : ∀ values,
        (({sample with targets := values} : CurvePublicSample).retargetMask input target).targets
          gate position = values gate position := by
      intro values
      simp only [CurvePublicSample.retargetMask]
      by_cases same : gate = 2
      · subst gate
        rw [Function.update_self]
        exact retargetBits_free _ _ position (by simpa using pivot)
      · rw [Function.update_of_ne same]
    simp_rw [unchanged]
    exact uniform_nested_eval gate position

private theorem uniform_product_map {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (first : A → C) (second : B → D)
    (firstLaw : (PMF.uniformOfFintype A).map first = PMF.uniformOfFintype C)
    (secondLaw : (PMF.uniformOfFintype B).map second = PMF.uniformOfFintype D) :
    (PMF.uniformOfFintype (A × B)).map (fun pair => (first pair.1, second pair.2)) =
      PMF.uniformOfFintype (C × D) := by
  calc
    _ = (PMF.uniformOfFintype B).bind fun b =>
        ((PMF.uniformOfFintype A).map first).map fun c => (c, second b) := by
      rw [uniform_prod_eq_bind, PMF.map_bind]
      simp only [PMF.map_comp, Function.comp_def]
    _ = ((PMF.uniformOfFintype B).map second).bind fun d =>
        (PMF.uniformOfFintype C).map fun c => (c, d) := by
      rw [firstLaw, PMF.bind_map]
      rfl
    _ = _ := by rw [secondLaw, ← uniform_prod_eq_bind]

private theorem uniform_nested_quotient_eval {Rows Positions : Type*}
    [Fintype Rows] [Fintype Positions] [DecidableEq Rows] [DecidableEq Positions]
    (row : Rows) (position : Positions) :
    (PMF.uniformOfFintype (Rows → Positions → HashLiftQuotient)).map
      (fun values => values row position) = PMF.uniformOfFintype HashLiftQuotient := by
  have law := congrArg (fun distribution => distribution.map (fun values => values position))
    (uniform_function_eval (Value := Positions → HashLiftQuotient) row)
  rw [PMF.map_comp, uniform_function_eval] at law
  exact law

/-- A selected field target keeps its independent uniform hash quotient. -/
theorem XPublicSample.target_quotient_uniform (visible : VisibleGateSample 5 4)
    (input : AffineInput) (target : BaseField)
    (gate : Fin 4) (position : Fin coordinateBitCount) :
    (PMF.uniformOfFintype (HiddenGateSample 4)).map (fun hidden =>
      ((XPublicSample.visibleHiddenEquiv.symm (visible, hidden)).retargetMask
        input target |>.targets gate position, hidden.2 gate position)) =
          PMF.uniformOfFintype (BaseField × HashLiftQuotient) := by
  let sample := XPublicSample.visibleHiddenEquiv.symm
    (visible, (fun _ _ => 0), (fun _ _ => defaultHashLiftQuotient))
  have functions : (fun hidden : HiddenGateSample 4 =>
      ((XPublicSample.visibleHiddenEquiv.symm (visible, hidden)).retargetMask
        input target |>.targets gate position, hidden.2 gate position)) =
      (fun hidden => ((({sample with targets := hidden.1} : XPublicSample).retargetMask
        input target).targets gate position, hidden.2 gate position)) := by
    funext hidden
    simp only [sample, XPublicSample.visibleHiddenEquiv, XPublicSample.retargetMask,
      XPublicSample.request, BiquadraticXRequest.result, Equiv.coe_fn_symm_mk]
  rw [functions]
  exact uniform_product_map
    (A := Fin 4 → Fin coordinateBitCount → BaseField)
    (B := Fin 4 → Fin coordinateBitCount → HashLiftQuotient)
    (C := BaseField) (D := HashLiftQuotient)
    (fun values => (({sample with targets := values} : XPublicSample).retargetMask
      input target).targets gate position)
    (fun quotients => quotients gate position)
    (XPublicSample.target_uniform sample input target gate position)
    (uniform_nested_quotient_eval gate position)

/-- A selected field target keeps its independent uniform hash quotient. -/
theorem YPublicSample.target_quotient_uniform (visible : VisibleGateSample 4 3)
    (input : AffineInput) (target : BaseField)
    (gate : Fin 3) (position : Fin coordinateBitCount) :
    (PMF.uniformOfFintype (HiddenGateSample 3)).map (fun hidden =>
      ((YPublicSample.visibleHiddenEquiv.symm (visible, hidden)).retargetMask
        input target |>.targets gate position, hidden.2 gate position)) =
          PMF.uniformOfFintype (BaseField × HashLiftQuotient) := by
  let sample := YPublicSample.visibleHiddenEquiv.symm
    (visible, (fun _ _ => 0), (fun _ _ => defaultHashLiftQuotient))
  have functions : (fun hidden : HiddenGateSample 3 =>
      ((YPublicSample.visibleHiddenEquiv.symm (visible, hidden)).retargetMask
        input target |>.targets gate position, hidden.2 gate position)) =
      (fun hidden => ((({sample with targets := hidden.1} : YPublicSample).retargetMask
        input target).targets gate position, hidden.2 gate position)) := by
    funext hidden
    simp only [sample, YPublicSample.visibleHiddenEquiv, YPublicSample.retargetMask,
      YPublicSample.request, BiquadraticYRequest.result, Equiv.coe_fn_symm_mk]
  rw [functions]
  exact uniform_product_map
    (A := Fin 3 → Fin coordinateBitCount → BaseField)
    (B := Fin 3 → Fin coordinateBitCount → HashLiftQuotient)
    (C := BaseField) (D := HashLiftQuotient)
    (fun values => (({sample with targets := values} : YPublicSample).retargetMask
      input target).targets gate position)
    (fun quotients => quotients gate position)
    (YPublicSample.target_uniform sample input target gate position)
    (uniform_nested_quotient_eval gate position)

/-- A selected field target keeps its independent uniform hash quotient. -/
theorem ZPublicSample.target_quotient_uniform (visible : VisibleGateSample 5 5)
    (input : AffineInput) (target : BaseField)
    (gate : Fin 5) (position : Fin coordinateBitCount) :
    (PMF.uniformOfFintype (HiddenGateSample 5)).map (fun hidden =>
      ((ZPublicSample.visibleHiddenEquiv.symm (visible, hidden)).retargetMask
        input target |>.targets gate position, hidden.2 gate position)) =
          PMF.uniformOfFintype (BaseField × HashLiftQuotient) := by
  let sample := ZPublicSample.visibleHiddenEquiv.symm
    (visible, (fun _ _ => 0), (fun _ _ => defaultHashLiftQuotient))
  have functions : (fun hidden : HiddenGateSample 5 =>
      ((ZPublicSample.visibleHiddenEquiv.symm (visible, hidden)).retargetMask
        input target |>.targets gate position, hidden.2 gate position)) =
      (fun hidden => ((({sample with targets := hidden.1} : ZPublicSample).retargetMask
        input target).targets gate position, hidden.2 gate position)) := by
    funext hidden
    simp only [sample, ZPublicSample.visibleHiddenEquiv, ZPublicSample.retargetMask,
      ZPublicSample.request, BiquadraticZRequest.result, Equiv.coe_fn_symm_mk]
  rw [functions]
  exact uniform_product_map
    (A := Fin 5 → Fin coordinateBitCount → BaseField)
    (B := Fin 5 → Fin coordinateBitCount → HashLiftQuotient)
    (C := BaseField) (D := HashLiftQuotient)
    (fun values => (({sample with targets := values} : ZPublicSample).retargetMask
      input target).targets gate position)
    (fun quotients => quotients gate position)
    (ZPublicSample.target_uniform sample input target gate position)
    (uniform_nested_quotient_eval gate position)

/-- A selected field target keeps its independent uniform hash quotient. -/
theorem CurvePublicSample.target_quotient_uniform (visible : VisibleGateSample 3 5)
    (input : AffineInput) (target : BaseField)
    (gate : Fin 5) (position : Fin coordinateBitCount) :
    (PMF.uniformOfFintype (HiddenGateSample 5)).map (fun hidden =>
      ((CurvePublicSample.visibleHiddenEquiv.symm (visible, hidden)).retargetMask
        input target |>.targets gate position, hidden.2 gate position)) =
          PMF.uniformOfFintype (BaseField × HashLiftQuotient) := by
  let sample := CurvePublicSample.visibleHiddenEquiv.symm
    (visible, (fun _ _ => 0), (fun _ _ => defaultHashLiftQuotient))
  have functions : (fun hidden : HiddenGateSample 5 =>
      ((CurvePublicSample.visibleHiddenEquiv.symm (visible, hidden)).retargetMask
        input target |>.targets gate position, hidden.2 gate position)) =
      (fun hidden => ((({sample with targets := hidden.1} : CurvePublicSample).retargetMask
        input target).targets gate position, hidden.2 gate position)) := by
    funext hidden
    simp only [sample, CurvePublicSample.visibleHiddenEquiv, CurvePublicSample.retargetMask,
      CurvePublicSample.request, CurveGateRequest.result, Equiv.coe_fn_symm_mk]
  rw [functions]
  exact uniform_product_map
    (A := Fin 5 → Fin coordinateBitCount → BaseField)
    (B := Fin 5 → Fin coordinateBitCount → HashLiftQuotient)
    (C := BaseField) (D := HashLiftQuotient)
    (fun values => (({sample with targets := values} : CurvePublicSample).retargetMask
      input target).targets gate position)
    (fun quotients => quotients gate position)
    (CurvePublicSample.target_uniform sample input target gate position)
    (uniform_nested_quotient_eval gate position)

/-- This index contains exactly the twelve point adaptor families. -/
abbrev PointGateFamily := Fin 4 ⊕ Fin 3 ⊕ Fin 5

def RowPublicSample.gateTargetQuotient (sample : RowPublicSample)
    (family : PointGateFamily) (position : Fin coordinateBitCount) :
    BaseField × HashLiftQuotient := match family with
  | .inl gate => (sample.x.targets gate position, sample.x.quotients gate position)
  | .inr (.inl gate) => (sample.y.targets gate position, sample.y.quotients gate position)
  | .inr (.inr gate) => (sample.z.targets gate position, sample.z.quotients gate position)

def VisibleRowSample.gateTable (visible : VisibleRowSample)
    (family : PointGateFamily) (position : Fin coordinateBitCount) : BitAdaptor.Table :=
  match family with
  | .inl gate => (visible.1.2 gate).get position
  | .inr (.inl gate) => (visible.2.1.2 gate).get position
  | .inr (.inr gate) => (visible.2.2.2 gate).get position

/-- Each actual selected point adaptor has the full uniform target-quotient marginal. -/
theorem RowPublicSample.target_quotient_uniform (visible : VisibleRowSample)
    (input : AffineInput) (target : FieldMacToECMac.HomogeneousValue)
    (family : PointGateFamily) (position : Fin coordinateBitCount) :
    (PMF.uniformOfFintype HiddenRowSample).map (fun hidden =>
      ((RowPublicSample.visibleHiddenEquiv.symm (visible, hidden)).retargetMask
        input target).gateTargetQuotient family position) =
          PMF.uniformOfFintype (BaseField × HashLiftQuotient) := by
  cases family with
  | inl gate =>
    have law := XPublicSample.target_quotient_uniform visible.1 input target.x gate position
    rw [← map_uniform_prod_fst (First := HiddenGateSample 4)
      (Second := HiddenGateSample 3 × HiddenGateSample 5), PMF.map_comp] at law
    exact law
  | inr family =>
    cases family with
    | inl gate =>
      have projection := congrArg (fun distribution => distribution.map Prod.fst)
        (map_uniform_prod_snd (First := HiddenGateSample 4)
          (Second := HiddenGateSample 3 × HiddenGateSample 5))
      rw [PMF.map_comp, map_uniform_prod_fst] at projection
      have law := YPublicSample.target_quotient_uniform visible.2.1 input target.y gate position
      rw [← projection, PMF.map_comp] at law
      exact law
    | inr gate =>
      have projection := congrArg (fun distribution => distribution.map Prod.snd)
        (map_uniform_prod_snd (First := HiddenGateSample 4)
          (Second := HiddenGateSample 3 × HiddenGateSample 5))
      rw [PMF.map_comp, map_uniform_prod_snd] at projection
      have law := ZPublicSample.target_quotient_uniform visible.2.2 input target.z gate position
      rw [← projection, PMF.map_comp] at law
      exact law

/-- This function reads one raw selected programming block before label XOR. -/
def selectedPointBlock (visible : VisibleRowSample) (hidden : HiddenRowSample)
    (input : AffineInput) (target : FieldMacToECMac.HomogeneousValue)
    (family : PointGateFamily) (position : Fin coordinateBitCount)
    (slot : Pipeline.FixedKeySlot) : Block :=
  let pair := ((RowPublicSample.visibleHiddenEquiv.symm (visible, hidden)).retargetMask
    input target).gateTargetQuotient family position
  match slot with
  | .hash index => liftHashBlocks (goodHashLift pair.1 pair.2).1 index
  | .pad index => targetPadBlocks (visible.gateTable family position) pair.1 index

/-- This density accounts for both field encoding and the complete-fiber hash source. -/
def activeSlotDensity [Fintype Block] : Pipeline.FixedKeySlot → ENNReal
  | .hash _ => (Fintype.card Block : ENNReal) ^ 2 /
      (baseFieldModulus * hashLiftQuotientCount : Nat)
  | .pad _ => (Fintype.card Block : ENNReal) / baseFieldModulus

/-- The selected point block has the required density for each fixed prefix. -/
theorem selectedPointBlock_mass_le [Fintype Block]
    (visible : VisibleRowSample) (input : AffineInput)
    (target : FieldMacToECMac.HomogeneousValue) (family : PointGateFamily)
    (position : Fin coordinateBitCount) (slot : Pipeline.FixedKeySlot) (block : Block) :
    (PMF.uniformOfFintype HiddenRowSample).toOuterMeasure
      {hidden | selectedPointBlock visible hidden input target family position slot = block} ≤
        activeSlotDensity slot := by
  have law := RowPublicSample.target_quotient_uniform visible input target family position
  cases slot with
  | hash index =>
    have bound := goodHashLiftBlocks_mass_le index block
    rw [← law, PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] at bound
    conv_lhs => arg 2; ext hidden; dsimp only [selectedPointBlock]
    conv_rhs => dsimp only [activeSlotDensity]
    exact bound
  | pad index =>
    have fields := congrArg (fun distribution => distribution.map Prod.fst) law
    rw [PMF.map_comp, map_uniform_prod_fst] at fields
    have bound := targetPadBlocks_mass_le (visible.gateTable family position) index block
    rw [← fields, PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] at bound
    conv at bound => lhs; arg 2; ext hidden; dsimp only [Function.comp_def]
    conv_lhs => arg 2; ext hidden; dsimp only [selectedPointBlock]
    conv_rhs => dsimp only [activeSlotDensity]
    exact bound

/-- An invariant shift preserves one fresh coordinate. -/
theorem uniform_nestedCoordinate_shift
    {Rows Positions : Type*} [Fintype Rows] [Fintype Positions]
    [DecidableEq Rows] [DecidableEq Positions] (row : Rows) (position : Positions)
    (shift : (Rows → Positions → BaseField) → BaseField)
    (shiftLaw : ∀ values seed,
      shift (Function.update values row (Function.update (values row) position seed)) = shift values) :
    (PMF.uniformOfFintype (Rows → Positions → BaseField)).map
      (fun values => values row position + shift values) = PMF.uniformOfFintype BaseField := by
  have law : (PMF.uniformOfFintype (Rows → Positions → BaseField)).map
      (fun values => -(values row position + shift values)) = PMF.uniformOfFintype BaseField := by
    apply uniform_affine_nestedCoordinate row position
    intro values seed
    rw [Function.update_self, Function.update_self, shiftLaw]
    ring
  have negative := congrArg (fun distribution => distribution.map (fun value : BaseField => -value)) law
  rw [PMF.map_comp] at negative
  have uniformNeg := map_uniformOfFintype_equivBetween (Equiv.neg BaseField)
  change (PMF.uniformOfFintype BaseField).map (fun value => -value) = _ at uniformNeg
  rw [uniformNeg] at negative
  simpa only [Function.comp_def, neg_neg] using negative

/-- These slopes invert the actual X selected-mask map. -/
def XPublicSample.branchSlope (sample : XPublicSample)
    (coefficients : Fin 4 → BaseField) (input : AffineInput) : Fin 4 → BaseField :=
  let r := fun index => sample.coefficients index.succ - coefficients index
  let y6 := (maskShiftEquiv (-r 2) input.y).symm (sample.targets 0)
  let y8 := (maskShiftEquiv (-r 3) input.y).symm (sample.targets 1)
  ![-r 2, -r 3, -(r 1 + DigitAdaptor.fromBits y8), -(r 0 + DigitAdaptor.fromBits y6)]

/-- Each X slope excludes its own target row. -/
theorem XPublicSample.branchSlope_own (sample : XPublicSample)
    (coefficients : Fin 4 → BaseField) (input : AffineInput)
    (gate : Fin 4) (values : Fin coordinateBitCount → BaseField) :
    ({sample with targets := Function.update sample.targets gate values} : XPublicSample).branchSlope
      coefficients input gate = sample.branchSlope coefficients input gate := by
  fin_cases gate <;> simp [XPublicSample.branchSlope]

/-- Every X slope excludes the free pivot seed row. -/
theorem XPublicSample.branchSlope_seed (sample : XPublicSample)
    (coefficients : Fin 4 → BaseField) (input : AffineInput)
    (gate : Fin 4) (values : Fin coordinateBitCount → BaseField) :
    ({sample with targets := Function.update sample.targets 2 values} : XPublicSample).branchSlope
      coefficients input gate = sample.branchSlope coefficients input gate := by
  simp [XPublicSample.branchSlope]

/-- These targets specify either actual branch for one X gate. -/
def XPublicSample.branchTarget (sample : XPublicSample) (coefficients : Fin 4 → BaseField)
    (input : AffineInput) (target : BaseField) (gate : Fin 4)
    (position : Fin coordinateBitCount) (selected branch : Bool) : BaseField :=
  (sample.retargetMask input target).targets gate position +
    (if branch then sample.branchSlope coefficients input gate else 0) -
    (if selected then sample.branchSlope coefficients input gate else 0)

local instance branchCoordinateNeZero : NeZero coordinateBitCount := ⟨by decide⟩

/-- Both X branch targets have uniform field marginals. -/
theorem XPublicSample.branchTarget_uniform (sample : XPublicSample)
    (coefficients : Fin 4 → BaseField) (input : AffineInput) (target : BaseField)
    (gate : Fin 4) (position : Fin coordinateBitCount) (selected branch : Bool) :
    (PMF.uniformOfFintype (Fin 4 → Fin coordinateBitCount → BaseField)).map
      (fun values => ({sample with targets := values} : XPublicSample).branchTarget
        coefficients input target gate position selected branch) = PMF.uniformOfFintype BaseField := by
  by_cases pivot : gate = 3 ∧ position = 0
  · rcases pivot with ⟨rfl, rfl⟩
    apply uniform_affine_nestedCoordinate 2 0
    intro values seed
    have targetLaw := XPublicSample.pivot_seed
      ({sample with targets := values} : XPublicSample) input target seed
    change (({sample with targets := (Function.update values 2
        (Function.update (values 2) 0 seed))} : XPublicSample).retargetMask input target).targets 3 0 =
      (({sample with targets := values} : XPublicSample).retargetMask input target).targets 3 0 +
        values 2 0 - seed at targetLaw
    have slopeLaw := XPublicSample.branchSlope_seed
      ({sample with targets := values} : XPublicSample) coefficients input 3
      (Function.update (values 2) 0 seed)
    simp only [XPublicSample.branchTarget]
    rw [targetLaw, slopeLaw]
    ring
  · have unchanged : ∀ values,
        (({sample with targets := values} : XPublicSample).retargetMask input target).targets
          gate position = values gate position := by
      intro values
      simp only [XPublicSample.retargetMask]
      by_cases same : gate = 3
      · subst gate
        rw [Function.update_self]
        have nonzero : position ≠ 0 := by simpa using pivot
        rcases (Fin.eq_zero_or_eq_succ position).resolve_left nonzero with ⟨index, rfl⟩
        rfl
      · rw [Function.update_of_ne same]
    simp only [XPublicSample.branchTarget, unchanged, sub_eq_add_neg, add_assoc]
    apply uniform_nestedCoordinate_shift gate position
    intro values seed
    have slopeLaw := XPublicSample.branchSlope_own
      ({sample with targets := values} : XPublicSample) coefficients input gate
      (Function.update (values gate) position seed)
    rw [slopeLaw]

/-- These slopes invert the actual Y selected-mask map. -/
def YPublicSample.branchSlope (sample : YPublicSample)
    (coefficients : Fin 3 → BaseField) (input : AffineInput) : Fin 3 → BaseField :=
  let r := fun index => sample.coefficients index.succ - coefficients index
  let y6 := (maskShiftEquiv (-r 2) input.x).symm (sample.targets 0)
  let x7 := (maskShiftEquiv (-(r 1 + DigitAdaptor.fromBits y6)) input.x).symm (sample.targets 1)
  ![-r 2, -(r 1 + DigitAdaptor.fromBits y6), -(r 0 + DigitAdaptor.fromBits x7)]

/-- Each Y slope excludes its own target row. -/
theorem YPublicSample.branchSlope_own (sample : YPublicSample)
    (coefficients : Fin 3 → BaseField) (input : AffineInput)
    (gate : Fin 3) (values : Fin coordinateBitCount → BaseField) :
    ({sample with targets := Function.update sample.targets gate values} : YPublicSample).branchSlope
      coefficients input gate = sample.branchSlope coefficients input gate := by
  fin_cases gate <;> simp [YPublicSample.branchSlope]

/-- Every Y slope excludes the free pivot seed row: the pivot row appears in no slope. -/
theorem YPublicSample.branchSlope_seed (sample : YPublicSample)
    (coefficients : Fin 3 → BaseField) (input : AffineInput)
    (gate : Fin 3) (values : Fin coordinateBitCount → BaseField) :
    ({sample with targets := Function.update sample.targets 2 values} : YPublicSample).branchSlope
      coefficients input gate = sample.branchSlope coefficients input gate := by
  simp [YPublicSample.branchSlope]

/-- These targets specify either actual branch for one Y gate. -/
def YPublicSample.branchTarget (sample : YPublicSample) (coefficients : Fin 3 → BaseField)
    (input : AffineInput) (target : BaseField) (gate : Fin 3)
    (position : Fin coordinateBitCount) (selected branch : Bool) : BaseField :=
  (sample.retargetMask input target).targets gate position +
    (if branch then sample.branchSlope coefficients input gate else 0) -
    (if selected then sample.branchSlope coefficients input gate else 0)

/-- Both Y branch targets have uniform field marginals. -/
theorem YPublicSample.branchTarget_uniform (sample : YPublicSample)
    (coefficients : Fin 3 → BaseField) (input : AffineInput) (target : BaseField)
    (gate : Fin 3) (position : Fin coordinateBitCount) (selected branch : Bool) :
    (PMF.uniformOfFintype (Fin 3 → Fin coordinateBitCount → BaseField)).map
      (fun values => ({sample with targets := values} : YPublicSample).branchTarget
        coefficients input target gate position selected branch) = PMF.uniformOfFintype BaseField := by
  by_cases pivot : gate = 2 ∧ position = 0
  · rcases pivot with ⟨rfl, rfl⟩
    apply uniform_affine_nestedCoordinate_scaled 2 1 2 twoInverse twoInverse_cancel
    intro values seed
    have targetLaw := YPublicSample.pivot_seed
      ({sample with targets := values} : YPublicSample) input target seed
    change (({sample with targets := (Function.update values 2
        (Function.update (values 2) 1 seed))} : YPublicSample).retargetMask input target).targets 2 0 =
      (({sample with targets := values} : YPublicSample).retargetMask input target).targets 2 0 +
        2 * values 2 1 - 2 * seed at targetLaw
    have slopeLaw := YPublicSample.branchSlope_seed
      ({sample with targets := values} : YPublicSample) coefficients input 2
      (Function.update (values 2) 1 seed)
    simp only [YPublicSample.branchTarget]
    rw [targetLaw, slopeLaw]
    ring
  · have unchanged : ∀ values,
        (({sample with targets := values} : YPublicSample).retargetMask input target).targets
          gate position = values gate position := by
      intro values
      simp only [YPublicSample.retargetMask]
      by_cases same : gate = 2
      · subst gate
        rw [Function.update_self]
        have nonzero : position ≠ 0 := by simpa using pivot
        rcases (Fin.eq_zero_or_eq_succ position).resolve_left nonzero with ⟨index, rfl⟩
        rfl
      · rw [Function.update_of_ne same]
    simp only [YPublicSample.branchTarget, unchanged, sub_eq_add_neg, add_assoc]
    apply uniform_nestedCoordinate_shift gate position
    intro values seed
    have slopeLaw := YPublicSample.branchSlope_own
      ({sample with targets := values} : YPublicSample) coefficients input gate
      (Function.update (values gate) position seed)
    rw [slopeLaw]

/-- These slopes invert the actual Z selected-mask map. -/
def ZPublicSample.branchSlope (sample : ZPublicSample)
    (coefficients : Fin 4 → BaseField) (input : AffineInput) : Fin 5 → BaseField :=
  let r := fun index => sample.coefficients index.succ - coefficients index
  let y6 := (maskShiftEquiv (-r 1) input.y).symm (sample.targets 0)
  let y8 := (maskShiftEquiv (-r 3) input.y).symm (sample.targets 1)
  let x7 := (maskShiftEquiv (-r 2) input.x).symm (sample.targets 3)
  ![-r 1, -r 3, -(r 0 + DigitAdaptor.fromBits y8), -r 2,
    -(DigitAdaptor.fromBits y6 + DigitAdaptor.fromBits x7)]

/-- Each Z slope excludes its own target row. -/
theorem ZPublicSample.branchSlope_own (sample : ZPublicSample)
    (coefficients : Fin 4 → BaseField) (input : AffineInput)
    (gate : Fin 5) (values : Fin coordinateBitCount → BaseField) :
    ({sample with targets := Function.update sample.targets gate values} : ZPublicSample).branchSlope
      coefficients input gate = sample.branchSlope coefficients input gate := by
  fin_cases gate <;> simp [ZPublicSample.branchSlope]

/-- Every Z slope excludes the free pivot seed row. -/
theorem ZPublicSample.branchSlope_seed (sample : ZPublicSample)
    (coefficients : Fin 4 → BaseField) (input : AffineInput)
    (gate : Fin 5) (values : Fin coordinateBitCount → BaseField) :
    ({sample with targets := Function.update sample.targets 2 values} : ZPublicSample).branchSlope
      coefficients input gate = sample.branchSlope coefficients input gate := by
  simp [ZPublicSample.branchSlope]

/-- These targets specify either actual branch for one Z gate. -/
def ZPublicSample.branchTarget (sample : ZPublicSample) (coefficients : Fin 4 → BaseField)
    (input : AffineInput) (target : BaseField) (gate : Fin 5)
    (position : Fin coordinateBitCount) (selected branch : Bool) : BaseField :=
  (sample.retargetMask input target).targets gate position +
    (if branch then sample.branchSlope coefficients input gate else 0) -
    (if selected then sample.branchSlope coefficients input gate else 0)

/-- Both Z branch targets have uniform field marginals. -/
theorem ZPublicSample.branchTarget_uniform (sample : ZPublicSample)
    (coefficients : Fin 4 → BaseField) (input : AffineInput) (target : BaseField)
    (gate : Fin 5) (position : Fin coordinateBitCount) (selected branch : Bool) :
    (PMF.uniformOfFintype (Fin 5 → Fin coordinateBitCount → BaseField)).map
      (fun values => ({sample with targets := values} : ZPublicSample).branchTarget
        coefficients input target gate position selected branch) = PMF.uniformOfFintype BaseField := by
  by_cases pivot : gate = 4 ∧ position = 0
  · rcases pivot with ⟨rfl, rfl⟩
    apply uniform_affine_nestedCoordinate 2 0
    intro values seed
    have targetLaw := ZPublicSample.pivot_seed
      ({sample with targets := values} : ZPublicSample) input target seed
    change (({sample with targets := (Function.update values 2
        (Function.update (values 2) 0 seed))} : ZPublicSample).retargetMask input target).targets 4 0 =
      (({sample with targets := values} : ZPublicSample).retargetMask input target).targets 4 0 +
        values 2 0 - seed at targetLaw
    have slopeLaw := ZPublicSample.branchSlope_seed
      ({sample with targets := values} : ZPublicSample) coefficients input 4
      (Function.update (values 2) 0 seed)
    simp only [ZPublicSample.branchTarget]
    rw [targetLaw, slopeLaw]
    ring
  · have unchanged : ∀ values,
        (({sample with targets := values} : ZPublicSample).retargetMask input target).targets
          gate position = values gate position := by
      intro values
      simp only [ZPublicSample.retargetMask]
      by_cases same : gate = 4
      · subst gate
        rw [Function.update_self]
        have nonzero : position ≠ 0 := by simpa using pivot
        rcases (Fin.eq_zero_or_eq_succ position).resolve_left nonzero with ⟨index, rfl⟩
        rfl
      · rw [Function.update_of_ne same]
    simp only [ZPublicSample.branchTarget, unchanged, sub_eq_add_neg, add_assoc]
    apply uniform_nestedCoordinate_shift gate position
    intro values seed
    have slopeLaw := ZPublicSample.branchSlope_own
      ({sample with targets := values} : ZPublicSample) coefficients input gate
      (Function.update (values gate) position seed)
    rw [slopeLaw]

/-- These slopes invert the actual Curve selected-mask map. -/
def CurvePublicSample.branchSlope (sample : CurvePublicSample)
    (mask : BaseField) (input : AffineInput) : Fin 5 → BaseField :=
  let r1 := sample.coefficients 1 - mask
  let r2 := sample.coefficients 2 + mask
  let x3 := (maskShiftEquiv (-r1) input.x).symm (sample.targets 0)
  let x5 := (maskShiftEquiv (-DigitAdaptor.fromBits x3) input.x).symm (sample.targets 1)
  let y4 := (maskShiftEquiv (-r2) input.y).symm (sample.targets 3)
  ![-r1, -DigitAdaptor.fromBits x3, -DigitAdaptor.fromBits x5, -r2,
    -DigitAdaptor.fromBits y4]

/-- Each Curve slope excludes its own target row. -/
theorem CurvePublicSample.branchSlope_own (sample : CurvePublicSample)
    (mask : BaseField) (input : AffineInput)
    (gate : Fin 5) (values : Fin coordinateBitCount → BaseField) :
    ({sample with targets := Function.update sample.targets gate values} : CurvePublicSample).branchSlope
      mask input gate = sample.branchSlope mask input gate := by
  fin_cases gate <;> simp [CurvePublicSample.branchSlope]

/-- Every Curve slope excludes the free pivot seed row. -/
theorem CurvePublicSample.branchSlope_seed (sample : CurvePublicSample)
    (mask : BaseField) (input : AffineInput)
    (gate : Fin 5) (values : Fin coordinateBitCount → BaseField) :
    ({sample with targets := Function.update sample.targets 4 values} : CurvePublicSample).branchSlope
      mask input gate = sample.branchSlope mask input gate := by
  simp [CurvePublicSample.branchSlope]

/-- These targets specify either actual branch for one Curve gate. -/
def CurvePublicSample.branchTarget (sample : CurvePublicSample) (mask : BaseField)
    (input : AffineInput) (target : BaseField) (gate : Fin 5)
    (position : Fin coordinateBitCount) (selected branch : Bool) : BaseField :=
  (sample.retargetMask input target).targets gate position +
    (if branch then sample.branchSlope mask input gate else 0) -
    (if selected then sample.branchSlope mask input gate else 0)

/-- Both Curve branch targets have uniform field marginals. -/
theorem CurvePublicSample.branchTarget_uniform (sample : CurvePublicSample)
    (mask : BaseField) (input : AffineInput) (target : BaseField)
    (gate : Fin 5) (position : Fin coordinateBitCount) (selected branch : Bool) :
    (PMF.uniformOfFintype (Fin 5 → Fin coordinateBitCount → BaseField)).map
      (fun values => ({sample with targets := values} : CurvePublicSample).branchTarget
        mask input target gate position selected branch) = PMF.uniformOfFintype BaseField := by
  by_cases pivot : gate = 2 ∧ position = 0
  · rcases pivot with ⟨rfl, rfl⟩
    apply uniform_affine_nestedCoordinate 4 0
    intro values seed
    have targetLaw := CurvePublicSample.pivot_seed
      ({sample with targets := values} : CurvePublicSample) input target seed
    change (({sample with targets := (Function.update values 4
        (Function.update (values 4) 0 seed))} : CurvePublicSample).retargetMask input target).targets 2 0 =
      (({sample with targets := values} : CurvePublicSample).retargetMask input target).targets 2 0 +
        values 4 0 - seed at targetLaw
    have slopeLaw := CurvePublicSample.branchSlope_seed
      ({sample with targets := values} : CurvePublicSample) mask input 2
      (Function.update (values 4) 0 seed)
    simp only [CurvePublicSample.branchTarget]
    rw [targetLaw, slopeLaw]
    ring
  · have unchanged : ∀ values,
        (({sample with targets := values} : CurvePublicSample).retargetMask input target).targets
          gate position = values gate position := by
      intro values
      simp only [CurvePublicSample.retargetMask]
      by_cases same : gate = 2
      · subst gate
        rw [Function.update_self]
        have nonzero : position ≠ 0 := by simpa using pivot
        rcases (Fin.eq_zero_or_eq_succ position).resolve_left nonzero with ⟨index, rfl⟩
        rfl
      · rw [Function.update_of_ne same]
    simp only [CurvePublicSample.branchTarget, unchanged, sub_eq_add_neg, add_assoc]
    apply uniform_nestedCoordinate_shift gate position
    intro values seed
    have slopeLaw := CurvePublicSample.branchSlope_own
      ({sample with targets := values} : CurvePublicSample) mask input gate
      (Function.update (values gate) position seed)
    rw [slopeLaw]

/-- The X false target is the actual reconstructed mask entry. -/
theorem XPublicSample.branchTarget_false_source (sample : XPublicSample)
    (coefficients : Fin 4 → BaseField) (input : AffineInput) (target : BaseField)
    (gate : Fin 4) (position : Fin coordinateBitCount) :
    sample.branchTarget coefficients input target gate position
      (coordinateValues (if gate = 3 then input.x else input.y) position) false =
      ((xMaskSelectedEquiv coefficients input).symm
        ((fun index => sample.coefficients index.succ),
          (sample.retargetMask input target).targets)).2 gate position := by
  dsimp only [xMaskSelectedEquiv]
  fin_cases gate <;>
    dsimp only [XPublicSample.branchTarget, XPublicSample.branchSlope, maskShiftEquiv,
      Equiv.coe_fn_symm_mk, Equiv.symm, Equiv.coe_fn_mk]
  all_goals simp [XPublicSample.retargetMask]; split_ifs <;> ring_nf

/-- The Y false target is the actual reconstructed mask entry. -/
theorem YPublicSample.branchTarget_false_source (sample : YPublicSample)
    (coefficients : Fin 3 → BaseField) (input : AffineInput) (target : BaseField)
    (gate : Fin 3) (position : Fin coordinateBitCount) :
    sample.branchTarget coefficients input target gate position
      (coordinateValues input.x position) false =
      ((yMaskSelectedEquiv coefficients input).symm
        ((fun index => sample.coefficients index.succ),
          (sample.retargetMask input target).targets)).2 gate position := by
  dsimp only [yMaskSelectedEquiv]
  fin_cases gate <;>
    dsimp only [YPublicSample.branchTarget, YPublicSample.branchSlope, maskShiftEquiv,
      Equiv.coe_fn_symm_mk, Equiv.symm, Equiv.coe_fn_mk]
  all_goals simp [YPublicSample.retargetMask]; split_ifs <;> ring_nf

/-- The Z false target is the actual reconstructed mask entry. -/
theorem ZPublicSample.branchTarget_false_source (sample : ZPublicSample)
    (coefficients : Fin 4 → BaseField) (input : AffineInput) (target : BaseField)
    (gate : Fin 5) (position : Fin coordinateBitCount) :
    sample.branchTarget coefficients input target gate position
      (coordinateValues (if gate.val < 3 then input.y else input.x) position) false =
      ((zMaskSelectedEquiv coefficients input).symm
        ((fun index => sample.coefficients index.succ),
          (sample.retargetMask input target).targets)).2 gate position := by
  dsimp only [zMaskSelectedEquiv]
  fin_cases gate <;>
    dsimp only [ZPublicSample.branchTarget, ZPublicSample.branchSlope, maskShiftEquiv,
      Equiv.coe_fn_symm_mk, Equiv.symm, Equiv.coe_fn_mk]
  all_goals simp [ZPublicSample.retargetMask]; split_ifs <;> ring_nf

/-- The Curve false target is the actual reconstructed mask entry. -/
theorem CurvePublicSample.branchTarget_false_source (sample : CurvePublicSample)
    (mask : BaseField) (input : AffineInput) (target : BaseField)
    (gate : Fin 5) (position : Fin coordinateBitCount) :
    sample.branchTarget mask input target gate position
      (coordinateValues (if gate.val < 3 then input.x else input.y) position) false =
      ((curveMaskShiftEquiv mask input).symm
        (![sample.coefficients 1, sample.coefficients 2],
          (sample.retargetMask input target).targets)).2 gate position := by
  dsimp only [curveMaskShiftEquiv]
  fin_cases gate <;>
    dsimp only [CurvePublicSample.branchTarget, CurvePublicSample.branchSlope, maskShiftEquiv,
      Equiv.coe_fn_symm_mk, Equiv.symm, Equiv.coe_fn_mk]
  all_goals simp [CurvePublicSample.retargetMask, Equiv.addLeft]; split_ifs <;> ring_nf

/-- The true target adds the actual branch slope to the false target. -/
theorem XPublicSample.branchTarget_true (sample : XPublicSample)
    (coefficients : Fin 4 → BaseField) (input : AffineInput) (target : BaseField)
    (gate : Fin 4) (position : Fin coordinateBitCount) (selected : Bool) :
    sample.branchTarget coefficients input target gate position selected true =
      sample.branchTarget coefficients input target gate position selected false +
        sample.branchSlope coefficients input gate := by
  simp only [XPublicSample.branchTarget, Bool.false_eq_true, if_false, if_true]
  ring

/-- The true target adds the actual branch slope to the false target. -/
theorem YPublicSample.branchTarget_true (sample : YPublicSample)
    (coefficients : Fin 3 → BaseField) (input : AffineInput) (target : BaseField)
    (gate : Fin 3) (position : Fin coordinateBitCount) (selected : Bool) :
    sample.branchTarget coefficients input target gate position selected true =
      sample.branchTarget coefficients input target gate position selected false +
        sample.branchSlope coefficients input gate := by
  simp only [YPublicSample.branchTarget, Bool.false_eq_true, if_false, if_true]
  ring

/-- The true target adds the actual branch slope to the false target. -/
theorem ZPublicSample.branchTarget_true (sample : ZPublicSample)
    (coefficients : Fin 4 → BaseField) (input : AffineInput) (target : BaseField)
    (gate : Fin 5) (position : Fin coordinateBitCount) (selected : Bool) :
    sample.branchTarget coefficients input target gate position selected true =
      sample.branchTarget coefficients input target gate position selected false +
        sample.branchSlope coefficients input gate := by
  simp only [ZPublicSample.branchTarget, Bool.false_eq_true, if_false, if_true]
  ring

/-- The true target adds the actual branch slope to the false target. -/
theorem CurvePublicSample.branchTarget_true (sample : CurvePublicSample)
    (mask : BaseField) (input : AffineInput) (target : BaseField)
    (gate : Fin 5) (position : Fin coordinateBitCount) (selected : Bool) :
    sample.branchTarget mask input target gate position selected true =
      sample.branchTarget mask input target gate position selected false +
        sample.branchSlope mask input gate := by
  simp only [CurvePublicSample.branchTarget, Bool.false_eq_true, if_false, if_true]
  ring


/-- Each actual branch field keeps its independent uniform hash quotient. -/
theorem XPublicSample.branchTarget_quotient_uniform
    (visible : VisibleGateSample 5 4) (coefficients : Fin 4 → BaseField)
    (input : AffineInput) (target : BaseField) (gate : Fin 4)
    (position : Fin coordinateBitCount) (selected branch : Bool) :
    (PMF.uniformOfFintype (HiddenGateSample 4)).map (fun hidden =>
      ((XPublicSample.visibleHiddenEquiv.symm (visible, hidden)).branchTarget
        coefficients input target gate position selected branch, hidden.2 gate position)) =
          PMF.uniformOfFintype (BaseField × HashLiftQuotient) := by
  let sample := XPublicSample.visibleHiddenEquiv.symm
    (visible, (fun _ _ => 0), (fun _ _ => defaultHashLiftQuotient))
  have functions : (fun hidden : HiddenGateSample 4 =>
      ((XPublicSample.visibleHiddenEquiv.symm (visible, hidden)).branchTarget
        coefficients input target gate position selected branch, hidden.2 gate position)) =
      (fun hidden => (({sample with targets := hidden.1} : XPublicSample).branchTarget
        coefficients input target gate position selected branch, hidden.2 gate position)) := by
    rfl
  rw [functions]
  exact uniform_product_map
    (A := Fin 4 → Fin coordinateBitCount → BaseField)
    (B := Fin 4 → Fin coordinateBitCount → HashLiftQuotient)
    (C := BaseField) (D := HashLiftQuotient)
    (fun values => ({sample with targets := values} : XPublicSample).branchTarget
      coefficients input target gate position selected branch)
    (fun quotients => quotients gate position)
    (XPublicSample.branchTarget_uniform sample coefficients input target gate position selected branch)
    (uniform_nested_quotient_eval gate position)

/-- Each actual branch field keeps its independent uniform hash quotient. -/
theorem YPublicSample.branchTarget_quotient_uniform
    (visible : VisibleGateSample 4 3) (coefficients : Fin 3 → BaseField)
    (input : AffineInput) (target : BaseField) (gate : Fin 3)
    (position : Fin coordinateBitCount) (selected branch : Bool) :
    (PMF.uniformOfFintype (HiddenGateSample 3)).map (fun hidden =>
      ((YPublicSample.visibleHiddenEquiv.symm (visible, hidden)).branchTarget
        coefficients input target gate position selected branch, hidden.2 gate position)) =
          PMF.uniformOfFintype (BaseField × HashLiftQuotient) := by
  let sample := YPublicSample.visibleHiddenEquiv.symm
    (visible, (fun _ _ => 0), (fun _ _ => defaultHashLiftQuotient))
  have functions : (fun hidden : HiddenGateSample 3 =>
      ((YPublicSample.visibleHiddenEquiv.symm (visible, hidden)).branchTarget
        coefficients input target gate position selected branch, hidden.2 gate position)) =
      (fun hidden => (({sample with targets := hidden.1} : YPublicSample).branchTarget
        coefficients input target gate position selected branch, hidden.2 gate position)) := by
    rfl
  rw [functions]
  exact uniform_product_map
    (A := Fin 3 → Fin coordinateBitCount → BaseField)
    (B := Fin 3 → Fin coordinateBitCount → HashLiftQuotient)
    (C := BaseField) (D := HashLiftQuotient)
    (fun values => ({sample with targets := values} : YPublicSample).branchTarget
      coefficients input target gate position selected branch)
    (fun quotients => quotients gate position)
    (YPublicSample.branchTarget_uniform sample coefficients input target gate position selected branch)
    (uniform_nested_quotient_eval gate position)

/-- Each actual branch field keeps its independent uniform hash quotient. -/
theorem ZPublicSample.branchTarget_quotient_uniform
    (visible : VisibleGateSample 5 5) (coefficients : Fin 4 → BaseField)
    (input : AffineInput) (target : BaseField) (gate : Fin 5)
    (position : Fin coordinateBitCount) (selected branch : Bool) :
    (PMF.uniformOfFintype (HiddenGateSample 5)).map (fun hidden =>
      ((ZPublicSample.visibleHiddenEquiv.symm (visible, hidden)).branchTarget
        coefficients input target gate position selected branch, hidden.2 gate position)) =
          PMF.uniformOfFintype (BaseField × HashLiftQuotient) := by
  let sample := ZPublicSample.visibleHiddenEquiv.symm
    (visible, (fun _ _ => 0), (fun _ _ => defaultHashLiftQuotient))
  have functions : (fun hidden : HiddenGateSample 5 =>
      ((ZPublicSample.visibleHiddenEquiv.symm (visible, hidden)).branchTarget
        coefficients input target gate position selected branch, hidden.2 gate position)) =
      (fun hidden => (({sample with targets := hidden.1} : ZPublicSample).branchTarget
        coefficients input target gate position selected branch, hidden.2 gate position)) := by
    rfl
  rw [functions]
  exact uniform_product_map
    (A := Fin 5 → Fin coordinateBitCount → BaseField)
    (B := Fin 5 → Fin coordinateBitCount → HashLiftQuotient)
    (C := BaseField) (D := HashLiftQuotient)
    (fun values => ({sample with targets := values} : ZPublicSample).branchTarget
      coefficients input target gate position selected branch)
    (fun quotients => quotients gate position)
    (ZPublicSample.branchTarget_uniform sample coefficients input target gate position selected branch)
    (uniform_nested_quotient_eval gate position)

/-- Each actual branch field keeps its independent uniform hash quotient. -/
theorem CurvePublicSample.branchTarget_quotient_uniform
    (visible : VisibleGateSample 3 5) (mask : BaseField)
    (input : AffineInput) (target : BaseField) (gate : Fin 5)
    (position : Fin coordinateBitCount) (selected branch : Bool) :
    (PMF.uniformOfFintype (HiddenGateSample 5)).map (fun hidden =>
      ((CurvePublicSample.visibleHiddenEquiv.symm (visible, hidden)).branchTarget
        mask input target gate position selected branch, hidden.2 gate position)) =
          PMF.uniformOfFintype (BaseField × HashLiftQuotient) := by
  let sample := CurvePublicSample.visibleHiddenEquiv.symm
    (visible, (fun _ _ => 0), (fun _ _ => defaultHashLiftQuotient))
  have functions : (fun hidden : HiddenGateSample 5 =>
      ((CurvePublicSample.visibleHiddenEquiv.symm (visible, hidden)).branchTarget
        mask input target gate position selected branch, hidden.2 gate position)) =
      (fun hidden => (({sample with targets := hidden.1} : CurvePublicSample).branchTarget
        mask input target gate position selected branch, hidden.2 gate position)) := by
    rfl
  rw [functions]
  exact uniform_product_map
    (A := Fin 5 → Fin coordinateBitCount → BaseField)
    (B := Fin 5 → Fin coordinateBitCount → HashLiftQuotient)
    (C := BaseField) (D := HashLiftQuotient)
    (fun values => ({sample with targets := values} : CurvePublicSample).branchTarget
      mask input target gate position selected branch)
    (fun quotients => quotients gate position)
    (CurvePublicSample.branchTarget_uniform sample mask input target gate position selected branch)
    (uniform_nested_quotient_eval gate position)


/-- This pair uses the actual reconstructed branch target and its hidden quotient. -/
def RowPublicSample.branchTargetQuotient (sample : RowPublicSample) (rows : Coordinates.Rows)
    (input : AffineInput) (target : FieldMacToECMac.HomogeneousValue)
    (family : PointGateFamily) (position : Fin coordinateBitCount) (branch : Bool) :
    BaseField × HashLiftQuotient :=
  match family with
  | .inl gate =>
      (sample.x.branchTarget ![rows.x.x, rows.x.y, rows.x.xy, rows.x.ySquared]
        input target.x gate position
        (coordinateValues (if gate = 3 then input.x else input.y) position) branch,
        sample.x.quotients gate position)
  | .inr (.inl gate) =>
      (sample.y.branchTarget ![rows.y.x, rows.y.xSquared, rows.y.ySquared]
        input target.y gate position
        (coordinateValues input.x position) branch,
        sample.y.quotients gate position)
  | .inr (.inr gate) =>
      (sample.z.branchTarget ![rows.z.y, rows.z.xy, rows.z.xSquared, rows.z.ySquared]
        input target.z gate position
        (coordinateValues (if gate.val < 3 then input.y else input.x) position) branch,
        sample.z.quotients gate position)

/-- Either branch field keeps the same uniform field-quotient law. -/
theorem RowPublicSample.branchTarget_quotient_uniform (visible : VisibleRowSample)
    (rows : Coordinates.Rows) (input : AffineInput) (target : FieldMacToECMac.HomogeneousValue)
    (family : PointGateFamily) (position : Fin coordinateBitCount) (branch : Bool) :
    (PMF.uniformOfFintype HiddenRowSample).map (fun hidden =>
      (RowPublicSample.visibleHiddenEquiv.symm (visible, hidden)).branchTargetQuotient
        rows input target family position branch) =
          PMF.uniformOfFintype (BaseField × HashLiftQuotient) := by
  cases family with
  | inl gate =>
    have law := XPublicSample.branchTarget_quotient_uniform visible.1
      ![rows.x.x, rows.x.y, rows.x.xy, rows.x.ySquared] input target.x gate position
      (coordinateValues (if gate = 3 then input.x else input.y) position) branch
    rw [← map_uniform_prod_fst (First := HiddenGateSample 4)
      (Second := HiddenGateSample 3 × HiddenGateSample 5), PMF.map_comp] at law
    exact law
  | inr family =>
    cases family with
    | inl gate =>
      have projection := congrArg (fun distribution => distribution.map Prod.fst)
        (map_uniform_prod_snd (First := HiddenGateSample 4)
          (Second := HiddenGateSample 3 × HiddenGateSample 5))
      rw [PMF.map_comp, map_uniform_prod_fst] at projection
      have law := YPublicSample.branchTarget_quotient_uniform visible.2.1
        ![rows.y.x, rows.y.xSquared, rows.y.ySquared] input target.y gate position
        (coordinateValues input.x position) branch
      rw [← projection, PMF.map_comp] at law
      exact law
    | inr gate =>
      have projection := congrArg (fun distribution => distribution.map Prod.snd)
        (map_uniform_prod_snd (First := HiddenGateSample 4)
          (Second := HiddenGateSample 3 × HiddenGateSample 5))
      rw [PMF.map_comp, map_uniform_prod_snd] at projection
      have law := ZPublicSample.branchTarget_quotient_uniform visible.2.2
        ![rows.z.y, rows.z.xy, rows.z.xSquared, rows.z.ySquared] input target.z gate position
        (coordinateValues (if gate.val < 3 then input.y else input.x) position) branch
      rw [← projection, PMF.map_comp] at law
      exact law

/-- These five offsets use false hash targets and true pad targets. -/
def pointBranchBlock (visible : VisibleRowSample) (hidden : HiddenRowSample)
    (rows : Coordinates.Rows) (input : AffineInput) (target : FieldMacToECMac.HomogeneousValue)
    (family : PointGateFamily) (position : Fin coordinateBitCount)
    (slot : Pipeline.FixedKeySlot) : Block :=
  match slot with
  | .hash index =>
      let pair := (RowPublicSample.visibleHiddenEquiv.symm (visible, hidden)).branchTargetQuotient
        rows input target family position false
      liftHashBlocks (goodHashLift pair.1 pair.2).1 index
  | .pad index =>
      let pair := (RowPublicSample.visibleHiddenEquiv.symm (visible, hidden)).branchTargetQuotient
        rows input target family position true
      targetPadBlocks (visible.gateTable family position) pair.1 index

/-- Each actual branch offset satisfies the same block density bound. -/
theorem pointBranchBlock_mass_le [Fintype Block] (visible : VisibleRowSample)
    (rows : Coordinates.Rows) (input : AffineInput) (target : FieldMacToECMac.HomogeneousValue)
    (family : PointGateFamily) (position : Fin coordinateBitCount)
    (slot : Pipeline.FixedKeySlot) (block : Block) :
    (PMF.uniformOfFintype HiddenRowSample).toOuterMeasure
      {hidden | pointBranchBlock visible hidden rows input target family position slot = block} ≤
        activeSlotDensity slot := by
  cases slot with
  | hash index =>
    have law := RowPublicSample.branchTarget_quotient_uniform visible rows input target family position false
    have bound := goodHashLiftBlocks_mass_le index block
    rw [← law, PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] at bound
    conv_lhs => arg 2; ext hidden; dsimp only [pointBranchBlock]
    conv_rhs => dsimp only [activeSlotDensity]
    exact bound
  | pad index =>
    have law := RowPublicSample.branchTarget_quotient_uniform visible rows input target family position true
    have fields := congrArg (fun distribution => distribution.map Prod.fst) law
    rw [PMF.map_comp, map_uniform_prod_fst] at fields
    have bound := targetPadBlocks_mass_le (visible.gateTable family position) index block
    rw [← fields, PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] at bound
    conv at bound => lhs; arg 2; ext hidden; dsimp only [Function.comp_def]
    conv_lhs => arg 2; ext hidden; dsimp only [pointBranchBlock]
    conv_rhs => dsimp only [activeSlotDensity]
    exact bound

/-- This bit selects the actual point gate branch. -/
def PointGateFamily.selectedBit (family : PointGateFamily) (input : AffineInput)
    (position : Fin coordinateBitCount) : Bool :=
  match family with
  | .inl gate => coordinateValues (if gate = 3 then input.x else input.y) position
  | .inr (.inl _) => coordinateValues input.x position
  | .inr (.inr gate) => coordinateValues (if gate.val < 3 then input.y else input.x) position

/-- The selected branch offset is the actual programmed block. -/
theorem pointBranchBlock_eq_selectedPointBlock (visible : VisibleRowSample)
    (hidden : HiddenRowSample) (rows : Coordinates.Rows) (input : AffineInput)
    (target : FieldMacToECMac.HomogeneousValue) (family : PointGateFamily)
    (position : Fin coordinateBitCount) (slot : Pipeline.FixedKeySlot)
    (active : match slot with
      | .hash _ => family.selectedBit input position = false
      | .pad _ => family.selectedBit input position = true) :
    pointBranchBlock visible hidden rows input target family position slot =
      selectedPointBlock visible hidden input target family position slot := by
  rcases family with gate | (gate | gate) <;> cases slot <;>
    simp only [PointGateFamily.selectedBit, Nat.lt_succ_iff] at active <;>
    simp [pointBranchBlock, selectedPointBlock, RowPublicSample.branchTargetQuotient,
      RowPublicSample.gateTargetQuotient, RowPublicSample.retargetMask,
      RowPublicSample.visibleHiddenEquiv, XPublicSample.branchTarget,
      YPublicSample.branchTarget, ZPublicSample.branchTarget, active]
  all_goals try rw [active]
  all_goals congr 3 <;> first | rfl | (try simp [Nat.lt_succ_iff, active])

private theorem uniform_two_evaluations {Index Value : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Value] [Nonempty Value]
    (first second : Index) (distinct : first ≠ second) :
    (PMF.uniformOfFintype (Index → Value)).map
      (fun values => (values first, values second)) = PMF.uniformOfFintype (Value × Value) := by
  let other : {index : Index // index ≠ first} := ⟨second, Ne.symm distinct⟩
  have law := congrArg (fun distribution => distribution.map
      (fun pair : Value × ({index : Index // index ≠ first} → Value) =>
        (pair.1, pair.2 other)))
    (map_uniformOfFintype_equivBetween (Equiv.piSplitAt first (fun _ => Value)))
  rw [PMF.map_comp] at law
  have productLaw := uniform_product_map
    (A := Value) (B := {index : Index // index ≠ first} → Value)
    (C := Value) (D := Value) id (fun values => values other)
    (PMF.map_id _) (uniform_function_eval other)
  dsimp only [id] at productLaw
  rw [productLaw] at law
  exact law

private theorem uniform_pair_event_le {Index Source Value : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Source] [Nonempty Source]
    (first second : Index) (distinct : first ≠ second)
    (left right : Source → Value) (event : Set (Index → Source)) (density : ENNReal)
    (eventEq : event = {sample | left (sample first) = right (sample second)})
    (pointwise : ∀ value, (PMF.uniformOfFintype Source).toOuterMeasure
      {sample | left sample = value} ≤ density) :
    (PMF.uniformOfFintype (Index → Source)).toOuterMeasure event ≤ density := by
  rw [eventEq]
  have pairLaw := uniform_two_evaluations (Value := Source) first second distinct
  have bound : (PMF.uniformOfFintype (Source × Source)).toOuterMeasure
      {sample | left sample.1 = right sample.2} ≤ density := by
    rw [uniform_prod_eq_bind, PMF.toOuterMeasure_bind_apply]
    calc
      _ ≤ ∑' sample, PMF.uniformOfFintype Source sample * density := by
        apply ENNReal.tsum_le_tsum
        intro sample
        apply mul_le_mul_right
        rw [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
        exact pointwise (right sample)
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rw [← pairLaw, PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] at bound
  exact bound

private theorem finite_four_union_le {Source A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (distribution : PMF Source) (events : A → B → C → D → Set Source)
    (event : Set Source) (density : C → ENNReal)
    (eventEq : event = ⋃ a, ⋃ b, ⋃ c, ⋃ d, events a b c d)
    (pointwise : ∀ a b c d, distribution.toOuterMeasure (events a b c d) ≤ density c) :
    distribution.toOuterMeasure event ≤ ∑ _a : A, ∑ _b : B, ∑ c : C, ∑ _d : D, density c := by
  rw [eventEq]
  apply (MeasureTheory.measure_iUnion_le _).trans
  rw [tsum_fintype]
  apply Finset.sum_le_sum
  intro a _
  apply (MeasureTheory.measure_iUnion_le _).trans
  rw [tsum_fintype]
  apply Finset.sum_le_sum
  intro b _
  apply (MeasureTheory.measure_iUnion_le _).trans
  rw [tsum_fintype]
  apply Finset.sum_le_sum
  intro c _
  apply (MeasureTheory.measure_iUnion_le _).trans
  rw [tsum_fintype]
  apply Finset.sum_le_sum
  intro d _
  exact pointwise a b c d

/-- This index counts each pair of distinct output rows once. -/
abbrev PointRowPair := Σ upper : Fin FieldMacToECMac.outputMacCount, Fin upper.val

def PointRowPair.lower (pair : PointRowPair) : Fin FieldMacToECMac.outputMacCount :=
  ⟨pair.2.val, pair.2.isLt.trans pair.1.isLt⟩

theorem PointRowPair.distinct (pair : PointRowPair) : pair.lower ≠ pair.1 := by
  intro equal
  have values := congrArg Fin.val equal
  exact (Nat.ne_of_lt pair.2.isLt) values

/-- This event tests point output collisions in every fixed slot. -/
def pointBranchCollision (visible : Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : AffineInput) (targets : Fin FieldMacToECMac.outputMacCount →
      FieldMacToECMac.HomogeneousValue)
    (hidden : Fin FieldMacToECMac.outputMacCount → HiddenRowSample) : Prop :=
  ∃ (family : PointGateFamily) (position : Fin coordinateBitCount)
      (slot : Pipeline.FixedKeySlot) (pair : PointRowPair),
    pointBranchBlock (visible pair.lower) (hidden pair.lower) (rows pair.lower) input (targets pair.lower)
      family position slot =
    pointBranchBlock (visible pair.1) (hidden pair.1) (rows pair.1) input (targets pair.1)
      family position slot

/-- A good point tape gives distinct offsets in every reconstructed slot. -/
theorem pointBranchCollision_false_injective
    (visible : Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : AffineInput) (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (hidden : Fin FieldMacToECMac.outputMacCount → HiddenRowSample)
    (good : ¬ pointBranchCollision visible rows input targets hidden)
    (family : PointGateFamily) (position : Fin coordinateBitCount) (slot : Pipeline.FixedKeySlot) :
    Function.Injective (fun row => pointBranchBlock (visible row) (hidden row) (rows row)
      input (targets row) family position slot) := by
  intro first second equal
  by_contra distinct
  rcases lt_or_gt_of_ne distinct with before | after
  · let pair : PointRowPair := ⟨second, ⟨first.val, before⟩⟩
    apply good
    refine ⟨family, position, slot, pair, ?_⟩
    have lower : pair.lower = first := Fin.ext rfl
    simpa only [lower] using equal
  · let pair : PointRowPair := ⟨first, ⟨second.val, after⟩⟩
    apply good
    refine ⟨family, position, slot, pair, ?_⟩
    have lower : pair.lower = second := Fin.ext rfl
    simpa only [lower] using equal.symm

/-- A good point tape gives distinct actual selected programming offsets. -/
theorem pointBranchCollision_false_selected_injective
    (visible : Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : AffineInput) (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (hidden : Fin FieldMacToECMac.outputMacCount → HiddenRowSample)
    (good : ¬ pointBranchCollision visible rows input targets hidden)
    (family : PointGateFamily) (position : Fin coordinateBitCount) (slot : Pipeline.FixedKeySlot)
    (active : match slot with
      | .hash _ => family.selectedBit input position = false
      | .pad _ => family.selectedBit input position = true) :
    Function.Injective (fun row => selectedPointBlock (visible row) (hidden row)
      input (targets row) family position slot) := by
  have equal : (fun row => pointBranchBlock (visible row) (hidden row) (rows row)
      input (targets row) family position slot) =
      (fun row => selectedPointBlock (visible row) (hidden row) input (targets row) family position slot) := by
    funext row
    exact pointBranchBlock_eq_selectedPointBlock _ _ _ _ _ _ _ _ active
  rw [← equal]
  exact pointBranchCollision_false_injective visible rows input targets hidden good family position slot

/-- Two actual rows collide with at most one slot density. -/
theorem pointBranchBlock_pair_mass_le [Fintype Block]
    (visible : Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : AffineInput) (targets : Fin FieldMacToECMac.outputMacCount →
      FieldMacToECMac.HomogeneousValue) (family : PointGateFamily)
    (position : Fin coordinateBitCount) (slot : Pipeline.FixedKeySlot) (pair : PointRowPair) :
    (PMF.uniformOfFintype (Fin FieldMacToECMac.outputMacCount → HiddenRowSample)).toOuterMeasure
      {hidden | pointBranchBlock (visible pair.lower) (hidden pair.lower) (rows pair.lower) input
          (targets pair.lower) family position slot =
        pointBranchBlock (visible pair.1) (hidden pair.1) (rows pair.1) input
          (targets pair.1) family position slot} ≤ activeSlotDensity slot :=
by
  have pointwise := fun block => @pointBranchBlock_mass_le ‹Fintype Block›
    (visible pair.lower) (rows pair.lower) input (targets pair.lower) family position slot block
  exact uniform_pair_event_le
    (Index := Fin FieldMacToECMac.outputMacCount) (Source := HiddenRowSample) (Value := Block)
    pair.lower pair.1 pair.distinct
    (fun sample => pointBranchBlock (visible pair.lower) sample (rows pair.lower) input
      (targets pair.lower) family position slot)
    (fun sample => pointBranchBlock (visible pair.1) sample (rows pair.1) input
      (targets pair.1) family position slot)
    {hidden | pointBranchBlock (visible pair.lower) (hidden pair.lower) (rows pair.lower) input
        (targets pair.lower) family position slot =
      pointBranchBlock (visible pair.1) (hidden pair.1) (rows pair.1) input
        (targets pair.1) family position slot}
    (activeSlotDensity slot) rfl (by
      intro value
      have bound := pointwise value
      conv_lhs => arg 2; ext sample; dsimp only
      exact bound)

/-- The point collision event uses one sum over row pairs. -/
theorem pointBranchCollision_mass_le [Fintype Block]
    (visible : Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : AffineInput) (targets : Fin FieldMacToECMac.outputMacCount →
      FieldMacToECMac.HomogeneousValue) :
    (PMF.uniformOfFintype (Fin FieldMacToECMac.outputMacCount → HiddenRowSample)).toOuterMeasure
      {hidden | pointBranchCollision visible rows input targets hidden} ≤
    ∑ _family : PointGateFamily, ∑ _position : Fin coordinateBitCount,
      ∑ slot : Pipeline.FixedKeySlot, ∑ _pair : PointRowPair, activeSlotDensity slot := by
  have pointwise := fun family position slot pair =>
    @pointBranchBlock_pair_mass_le ‹Fintype Block› visible rows input targets family position slot pair
  exact finite_four_union_le
    (PMF.uniformOfFintype (Fin FieldMacToECMac.outputMacCount → HiddenRowSample))
    (fun family position slot (pair : PointRowPair) =>
      {hidden | pointBranchBlock (visible pair.lower) (hidden pair.lower) (rows pair.lower) input
          (targets pair.lower) family position slot =
        pointBranchBlock (visible pair.1) (hidden pair.1) (rows pair.1) input
          (targets pair.1) family position slot})
    {hidden | pointBranchCollision visible rows input targets hidden} activeSlotDensity
    (by ext hidden; simp only [pointBranchCollision, Set.mem_setOf_eq, Set.mem_iUnion])
    (by
      intro family position slot pair
      have bound := pointwise family position slot pair
      conv_lhs => arg 2; ext hidden; dsimp only
      exact bound)

/-- The row-pair index has 4095 elements. -/
theorem pointRowPair_card : Fintype.card PointRowPair = 4095 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : Nat => i), Finset.sum_range_id]
  rfl

/-- The five slots have total density at most eighteen inverse blocks. -/
theorem activeSlotDensity_sum_le [Fintype Block] :
    ∑ slot, activeSlotDensity slot ≤ 18 / (2 : ENNReal) ^ 128 := by
  let equiv : Pipeline.FixedKeySlot ≃ Fin 3 ⊕ Fin 2 := {
    toFun := fun slot => match slot with | .hash i => .inl i | .pad i => .inr i
    invFun := fun slot => match slot with | .inl i => .hash i | .inr i => .pad i
    left_inv := by intro slot; cases slot <;> rfl
    right_inv := by intro slot; cases slot <;> rfl }
  rw [← equiv.symm.sum_comp, Fintype.sum_sum_type]
  calc
    _ ≤ (∑ _i : Fin 3, 2 / (2 : ENNReal) ^ 128) +
        ∑ _i : Fin 2, 6 / (2 : ENNReal) ^ 128 := by
      apply add_le_add
      · exact Finset.sum_le_sum fun _ _ => hashDensity_le_two
      · exact Finset.sum_le_sum fun _ _ => padDensity_le_six
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp only [div_eq_mul_inv]
      norm_num
      ring

/-- The point birthday term uses the actual independent row sources. -/
theorem pointBranchCollision_mass_le_blocks [Fintype Block]
    (visible : Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : AffineInput) (targets : Fin FieldMacToECMac.outputMacCount →
      FieldMacToECMac.HomogeneousValue) :
    (PMF.uniformOfFintype (Fin FieldMacToECMac.outputMacCount → HiddenRowSample)).toOuterMeasure
      {hidden | pointBranchCollision visible rows input targets hidden} ≤
        224668080 / (2 : ENNReal) ^ 128 := by
  have bound := @pointBranchCollision_mass_le ‹Fintype Block› visible rows input targets
  apply bound.trans
  simp only [Finset.sum_const, Finset.card_univ, pointRowPair_card, nsmul_eq_mul,
    ← Finset.mul_sum, Fintype.card_fin]
  have bound := mul_le_mul_right activeSlotDensity_sum_le
    (12 * 254 * 4095 : ENNReal)
  convert bound using 1 <;>
    norm_num [PointGateFamily, coordinateBitCount, Fintype.card_sum, Fintype.card_fin,
      mul_assoc, ← mul_div_assoc] <;> first | rfl | ring

private theorem uniform_snd_event_le {A B : Type*}
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] [Nonempty (A × B)]
    (event : Set B) (joint : Set (A × B)) (density : ENNReal)
    (jointEq : joint = Prod.snd ⁻¹' event)
    (bound : (PMF.uniformOfFintype B).toOuterMeasure event ≤ density) :
    (PMF.uniformOfFintype (A × B)).toOuterMeasure joint ≤ density := by
  rw [jointEq, ← PMF.toOuterMeasure_map_apply, map_uniform_prod_snd]
  exact bound

/-- The unused curve tape does not change the point birthday bound. -/
theorem pointBranchCollision_fullTape_mass_le_blocks [Fintype Block]
    (visible : Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : AffineInput) (targets : Fin FieldMacToECMac.outputMacCount →
      FieldMacToECMac.HomogeneousValue) :
    (PMF.uniformOfFintype HiddenPublicSample).toOuterMeasure
      {hidden | pointBranchCollision visible rows input targets hidden.2} ≤
        224668080 / (2 : ENNReal) ^ 128 := by
  have bound := @pointBranchCollision_mass_le_blocks ‹Fintype Block› visible rows input targets
  have lifted := uniform_snd_event_le
    (A := HiddenGateSample 5) (B := Fin FieldMacToECMac.outputMacCount → HiddenRowSample)
    {hidden | pointBranchCollision visible rows input targets hidden}
    {hidden | pointBranchCollision visible rows input targets hidden.2}
    (224668080 / (2 : ENNReal) ^ 128) rfl bound
  dsimp only [HiddenPublicSample]
  exact lifted

private theorem outerMeasure_bind_le {A B : Type*} (source : PMF A)
    (next : A → PMF B) (event : Set B) (bound : ENNReal)
    (pointwise : ∀ sample, (next sample).toOuterMeasure event ≤ bound) :
    (source.bind next).toOuterMeasure event ≤ bound :=
  Probability.bind_event_le source next event bound (fun sample _ => pointwise sample)

private theorem four_bind_event_le {A B C D Result : Type*}
    (first : PMF A) (second : A → PMF B) (third : A → B → PMF C)
    (fourth : A → B → C → PMF D) (next : A → B → C → D → PMF Result)
    (distribution : PMF Result) (event : Set Result) (density : ENNReal)
    (law : distribution = first.bind fun a => (second a).bind fun b =>
      (third a b).bind fun c => (fourth a b c).bind (next a b c))
    (pointwise : ∀ a b c d, (next a b c d).toOuterMeasure event ≤ density) :
    distribution.toOuterMeasure event ≤ density := by
  rw [law]
  apply outerMeasure_bind_le
  intro a
  apply outerMeasure_bind_le
  intro b
  apply outerMeasure_bind_le
  intro c
  apply outerMeasure_bind_le
  exact pointwise a b c

universe uAux

private theorem option_decide_mass_le {Source Value : Type*} (source : PMF Source)
    (outcome : Option Value) (event : Value → Source → Prop) (density : ENNReal)
    (bound : ∀ value, source.toOuterMeasure {sample | event value sample} ≤ density) :
    (source.map (fun sample => outcome.elim false
      (fun value => @decide (event value sample) (Classical.propDecidable _)))).toOuterMeasure
        {flag | flag = true} ≤ density := by
  rw [PMF.toOuterMeasure_map_apply]
  cases outcome with
  | none => simp only [Option.elim, Set.preimage_setOf_eq, Bool.false_eq_true, Set.setOf_false,
      MeasureTheory.measure_empty]; exact bot_le
  | some value => simpa only [Option.elim, Set.preimage_setOf_eq, decide_eq_true_eq] using bound value

variable {Aux : Type uAux}
  (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec
    AffineInput Pipeline.Table Garbling.Labels Aux)
  (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)

/-- This internal prefix retains the state until the simulator encodes its input. -/
def idealCircuitPrefix :
    PMF (Pipeline.Table × (AffineInput × adversary.State) × CircuitSimulatorState ×
      List (Sigma Garbling.oracleSpec.Answer)) :=
  (simulatorStateTape parameter (Garbling.topology scalar)).bind fun state =>
    (runOracleProgramWithTranscript circuitSimulatorOracleHandler
      (adversary.chooseInput parameter state.table auxiliary) state).map
        (fun selected => (state.table, selected))

/-- The actual prefix reads only the public table and the independent oracle coin. -/
theorem idealCircuitPrefix_oracle :
    idealCircuitPrefix adversary parameter scalar auxiliary =
      (simulatorStateTape parameter (Garbling.topology scalar)).bind fun state =>
        (runOracleProgramWithTranscript idealOracleHandler
          (adversary.chooseInput parameter state.table auxiliary) state.oracle).map
            (fun selected => (state.table, selected.1,
              {state with oracle := selected.2.1}, selected.2.2)) := by
  unfold idealCircuitPrefix
  congr 1
  funext state
  rw [runCircuitSimulatorWithTranscript, PMF.map_comp]
  rfl

/-- The hidden target tape stays independent of the full adaptive prefix. -/
theorem idealCircuitPrefix_hidden :
    idealCircuitPrefix adversary parameter scalar auxiliary =
      (PMF.uniformOfFintype VisibleSimulatorCoin).bind fun visible =>
        let base := (SimulatorCoin.visibleHiddenEquiv.symm
          (visible, Classical.arbitrary HiddenPublicSample)).state
        (runOracleProgramWithTranscript idealOracleHandler
          (adversary.chooseInput parameter base.table auxiliary) base.oracle).bind fun selected =>
            (PMF.uniformOfFintype HiddenPublicSample).map fun hidden =>
              (base.table, selected.1,
                {(SimulatorCoin.visibleHiddenEquiv.symm (visible, hidden)).state with
                  oracle := selected.2.1}, selected.2.2) := by
  rw [idealCircuitPrefix_oracle]
  unfold simulatorStateTape
  rw [PMF.bind_map, uniform_simulatorCoin_split, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  congr 1
  funext visible
  have tables := fun hidden => simulatorCoin_hidden_table visible hidden
    (Classical.arbitrary HiddenPublicSample)
  have oracles := fun hidden => simulatorCoin_hidden_oracle visible hidden
    (Classical.arbitrary HiddenPublicSample)
  simp_rw [tables, oracles]
  simp only [PMF.map, Function.comp_def]
  exact PMF.bind_comm _ _ _

variable [FieldCertificate] [GroupCertificate] (construction : Construction)


/-- This type is the actual online free-point and scale coin. -/
abbrev CircuitOnlineCoin := (Fin 90 → Point) ×
  (Fin FieldMacToECMac.outputMacCount → NonZeroBase)

private def pointBranchTargets (point : Point) (online : CircuitOnlineCoin) :
    Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue :=
  fun row => (outputTargets point (Vector.ofFn online.1) online.2).get row

private def pointBranchEvent
    (visible : Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : AffineInput) (online : CircuitOnlineCoin) (point : Point)
    (hidden : HiddenPublicSample) : Prop :=
  pointBranchCollision visible rows input
    (pointBranchTargets point online) hidden.2

private theorem pointBranchEvent_mass_le [Fintype Block]
    (visible : Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : AffineInput) (online : CircuitOnlineCoin) (point : Point) :
    (PMF.uniformOfFintype HiddenPublicSample).toOuterMeasure
      {hidden | pointBranchEvent visible rows input online point hidden} ≤
        224668080 / (2 : ENNReal) ^ 128 := by
  have events : {hidden | pointBranchEvent visible rows input online point hidden} =
      {hidden | pointBranchCollision visible rows input (pointBranchTargets point online) hidden.2} := rfl
  have law := congrArg (fun event : Set HiddenPublicSample =>
    (PMF.uniformOfFintype HiddenPublicSample).toOuterMeasure event ≤
      224668080 / (2 : ENNReal) ^ 128) events
  exact Eq.mpr law (@pointBranchCollision_fullTape_mass_le_blocks ‹Fintype Block›
    visible rows input (pointBranchTargets point online))

private def idealPointBranchPrior (visible : VisibleSimulatorCoin) :=
  let base := (SimulatorCoin.visibleHiddenEquiv.symm
    (visible, Classical.arbitrary HiddenPublicSample)).state
  runOracleProgramWithTranscript idealOracleHandler
    (adversary.chooseInput parameter base.table auxiliary) base.oracle

private def idealPointBranchFinish (visible : VisibleSimulatorCoin)
    (selected : (AffineInput × adversary.State) × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))
    (online : CircuitOnlineCoin) (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows) : PMF Bool :=
  (PMF.uniformOfFintype HiddenPublicSample).map fun hidden =>
    ((Garbling.garbledCircuit construction).function scalar selected.1.1).elim false
      (fun point => @decide (pointBranchEvent visible.1.2 rows selected.1.1 online point hidden)
        (Classical.propDecidable _))

/-- This flag hides all target seeds and tests the five reconstructed point offsets. -/
def idealPointBranchCollisionFlag
    (reconstructRows : VisibleSimulatorCoin →
      ((AffineInput × adversary.State) × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)) →
      CircuitOnlineCoin → PMF (Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)) : PMF Bool :=
  (PMF.uniformOfFintype VisibleSimulatorCoin).bind fun visible =>
    (idealPointBranchPrior adversary parameter auxiliary visible).bind fun selected =>
      (PMF.uniformOfFintype CircuitOnlineCoin).bind fun online =>
        (reconstructRows visible selected online).bind fun rows =>
          idealPointBranchFinish adversary scalar construction visible selected online rows

private theorem idealPointBranchFinish_mass_le [Fintype Block]
    (visible : VisibleSimulatorCoin)
    (selected : (AffineInput × adversary.State) × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))
    (online : CircuitOnlineCoin) (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows) :
    (idealPointBranchFinish adversary scalar construction visible selected online rows).toOuterMeasure
      {flag | flag = true} ≤ 224668080 / (2 : ENNReal) ^ 128 := by
  dsimp only [idealPointBranchFinish]
  have bound := option_decide_mass_le (Source := HiddenPublicSample) (Value := Point)
    (PMF.uniformOfFintype HiddenPublicSample)
    ((Garbling.garbledCircuit construction).function scalar selected.1.1)
    (pointBranchEvent visible.1.2 rows selected.1.1 online)
    (224668080 / (2 : ENNReal) ^ 128)
    (pointBranchEvent_mass_le visible.1.2 rows selected.1.1 online)
  exact bound

/-- Any row reconstruction that excludes the hidden seeds satisfies this bound. -/
theorem idealPointBranchCollisionFlag_mass_le [Fintype Block]
    (reconstructRows : VisibleSimulatorCoin →
      ((AffineInput × adversary.State) × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)) →
      CircuitOnlineCoin → PMF (Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)) :
    (idealPointBranchCollisionFlag adversary parameter scalar auxiliary construction reconstructRows).toOuterMeasure
      {flag | flag = true} ≤ 224668080 / (2 : ENNReal) ^ 128 := by
  refine four_bind_event_le (PMF.uniformOfFintype VisibleSimulatorCoin)
    (idealPointBranchPrior adversary parameter auxiliary)
    (fun _ _ => PMF.uniformOfFintype CircuitOnlineCoin) reconstructRows
    (idealPointBranchFinish adversary scalar construction)
    (idealPointBranchCollisionFlag adversary parameter scalar auxiliary construction reconstructRows)
    {flag | flag = true} (224668080 / (2 : ENNReal) ^ 128) rfl ?_
  exact idealPointBranchFinish_mass_le adversary scalar construction

/-- This experiment adds only the actual encode collision flag to the public transcript. -/
def idealCircuitTranscriptWithBad :
    PMF (AdaptiveTranscript Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels × Bool) :=
  (idealCircuitPrefix adversary parameter scalar auxiliary).bind fun selected =>
    (concreteCircuitSimulator.simulateEncode selected.2.2.1 selected.2.1.1
      ((Garbling.garbledCircuit construction).function scalar selected.2.1.1)).bind fun encoded =>
        (runOracleProgramWithTranscript circuitSimulatorOracleHandler
          (adversary.decide parameter selected.1 encoded.1 auxiliary selected.2.1.2)
          encoded.2).map fun decided =>
            (⟨selected.1, selected.2.1.1, encoded.1, selected.2.2.2,
              decided.2.2, decided.1⟩, encoded.2.oracle.bad)

/-- Erasing the flag gives the actual ideal adaptive transcript. -/
theorem idealCircuitTranscriptWithBad_erase :
    (idealCircuitTranscriptWithBad adversary parameter scalar auxiliary construction).map Prod.fst =
      idealAdaptiveTranscript (Garbling.garbledCircuit construction) Garbling.topology
        concreteCircuitSimulator circuitSimulatorOracleHandler adversary
        parameter scalar auxiliary := by
  simp only [idealCircuitTranscriptWithBad, idealCircuitPrefix, idealAdaptiveTranscript,
    concreteCircuitSimulator, circuitSimulator, PMF.map_bind, PMF.bind_bind,
    PMF.bind_map, PMF.map_comp, Function.comp_def]

/-- The decision program does not change the encode collision probability. -/
theorem idealCircuitTranscriptWithBad_flag :
    (idealCircuitTranscriptWithBad adversary parameter scalar auxiliary construction).map Prod.snd =
      (idealCircuitPrefix adversary parameter scalar auxiliary).bind fun selected =>
        (concreteCircuitSimulator.simulateEncode selected.2.2.1 selected.2.1.1
          ((Garbling.garbledCircuit construction).function scalar selected.2.1.1)).map
            (fun encoded => encoded.2.oracle.bad) := by
  simp only [idealCircuitTranscriptWithBad, PMF.map_bind, PMF.map_comp]
  congr 1
  funext selected
  simp only [Function.comp_def, PMF.map, PMF.bind_const]

end

end Kriterion.ArgoMAC.Security
