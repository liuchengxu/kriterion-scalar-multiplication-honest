import Proof.Privacy.Collision.ActualScheduleFreshness
import Proof.Privacy.Collision.AdaptiveLabelCollision

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

/-- These offsets retain the actual source slopes, full lifts, and tables. -/
def circuitSourceOffset (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (gate : RawCircuitGate) : Pipeline.FixedKeySlot → Block
  | .hash slot => fullHashLiftBlockEquiv (lifts gate) slot
  | .pad slot => targetPadBlocks (circuitSourceTable source gate)
      (circuitSourceSlope source gate + ((lifts gate).val : BaseField)) slot

/-- These uses test the actual raw source against each prefix query. -/
def sourcePrequeryLabelUses (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (query : Fin history.length) (row : Fin (circuitBucketSize (history.get query).index)) :
    PrequeryLabelUse :=
  let index := (history.get query).index
  let gate := circuitBucketGate index row
  actualGateLabelUse oracle bridgeKey gate (rawSlotBranch index.slot)
    (circuitSourceOffset source lifts gate index.slot)

private theorem rawSourceRecord_domain (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift) (key : InputMacKey)
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot) :
    let pointKey := EncPRF.transformKey oracle.encOracle
      (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key
    ((sourceGatePrescription source pointKey key lifts gate).slotRecord slot).domain =
      BitAdaptor.encode (circuitGateKey pointKey key gate) (rawSlotBranch slot) ^^^
        (rawCircuitLocation gate).tweak := by
  cases slot <;> rfl

private theorem rawSourceRecord_range (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift) (key : InputMacKey)
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot) :
    let pointKey := EncPRF.transformKey oracle.encOracle
      (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key
    ((sourceGatePrescription source pointKey key lifts gate).slotRecord slot).range =
      circuitSourceOffset source lifts gate slot ^^^
        BitAdaptor.encode (circuitGateKey pointKey key gate) (rawSlotBranch slot) := by
  cases slot <;> rfl

/-- A good actual label flag gives prefix freshness for every raw gate slot. -/
theorem sourcePrequeryLabelCollision_false_fresh
    (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block)) (key : InputMacKey)
    (good : ¬ prequeryLabelCollision history
      (sourcePrequeryLabelUses oracle bridgeKey source lifts history) key)
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot) :
    let pointKey := EncPRF.transformKey oracle.encOracle
      (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key
    let record := (sourceGatePrescription source pointKey key lifts gate).slotRecord slot
    FreshPermutationPair history record.index record.domain record.range := by
  dsimp only
  intro prior member sameIndex
  obtain ⟨query, queryEqual⟩ := List.mem_iff_get.mp member
  let pointKey := EncPRF.transformKey oracle.encOracle
    (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key
  let keys := circuitGateKey pointKey key
  let slopes := circuitSourceSlope source
  let tables := circuitSourceTable source
  let index := (history.get query).index
  have bucket : fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot = index := by
    dsimp only [index]
    rw [queryEqual]
    exact sameIndex.symm
  let use : RawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index := ⟨(gate, slot), bucket⟩
  obtain ⟨row, rowEqual⟩ := circuitBucketUse_surjective keys slopes lifts tables index use
  have gateEqual : circuitBucketGate index row = gate := congrArg (fun use => use.1.1) rowEqual
  have slotEqual : index.slot = slot := congrArg (fun use => use.1.2) rowEqual
  have domainLaw := actualGateLabelUse_domain oracle bridgeKey key gate (rawSlotBranch slot)
    (circuitSourceOffset source lifts gate slot)
  have rangeLaw := actualGateLabelUse_range oracle bridgeKey key gate (rawSlotBranch slot)
    (circuitSourceOffset source lifts gate slot)
  have selectedUse : sourcePrequeryLabelUses oracle bridgeKey source lifts history query row =
      actualGateLabelUse oracle bridgeKey gate (rawSlotBranch slot) (circuitSourceOffset source lifts gate slot) := by
    change actualGateLabelUse oracle bridgeKey (circuitBucketGate index row) (rawSlotBranch index.slot)
      (circuitSourceOffset source lifts (circuitBucketGate index row) index.slot) = _
    rw [gateEqual, slotEqual]
  constructor
  · intro equal
    apply good
    refine ⟨query, row, Or.inl ?_⟩
    rw [selectedUse, domainLaw, queryEqual]
    exact (rawSourceRecord_domain oracle bridgeKey source lifts key gate slot).symm.trans equal.symm
  · intro equal
    apply good
    refine ⟨query, row, Or.inr ?_⟩
    rw [selectedUse, rangeLaw, queryEqual]
    exact (rawSourceRecord_range oracle bridgeKey source lifts key gate slot).symm.trans equal.symm

section PrequeryMass

attribute [local instance] publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The actual source flag pays the checked prefix label loss. -/
theorem sourcePrequeryLabelCollision_mass_le [Fintype Block]
    (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block)) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
      {key | prequeryLabelCollision history
        (sourcePrequeryLabelUses oracle bridgeKey source lifts history) key} ≤
      (182 * history.length : Nat) / (2 : ENNReal) ^ 128 := by
  have card : Fintype.card Block = 2 ^ 128 :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  simpa only [card, Nat.cast_pow, Nat.cast_ofNat] using
    prequeryLabelCollision_mass_le history (sourcePrequeryLabelUses oracle bridgeKey source lifts history)

end PrequeryMass

/-- This source inverts the selected mask data and retains every table and quotient. -/
def circuitMaskSourceFromSelected (sample : PublicSample) (mask : BaseField)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows) (input : AffineInput) : CircuitMaskSample :=
  (((curveMaskShiftEquiv mask input).symm
      (![sample.curve.coefficients 1, sample.curve.coefficients 2],
        sample.curve.targets),
      sample.curve.tables, sample.curve.quotients),
    fun row =>
      let value := sample.points.get row
      (((xMaskSelectedEquiv ![(rows row).x.x, (rows row).x.y, (rows row).x.xy,
          (rows row).x.ySquared] input).symm
          ((fun index => value.x.coefficients index.succ),
            value.x.targets), value.x.tables, value.x.quotients),
        ((yMaskSelectedEquiv ![(rows row).y.x, (rows row).y.xSquared, (rows row).y.ySquared] input).symm
          ((fun index => value.y.coefficients index.succ),
            value.y.targets), value.y.tables, value.y.quotients),
        ((zMaskSelectedEquiv ![(rows row).z.y, (rows row).z.xy, (rows row).z.xSquared,
          (rows row).z.ySquared] input).symm
          ((fun index => value.z.coefficients index.succ),
            value.z.targets), value.z.tables, value.z.quotients)))


/-- The selected source uses the actual retargeted public sample. -/
def reconstructedCircuitSource (sample : PublicSample) (mask : BaseField)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows) (input : AffineInput)
    (curveTarget : BaseField)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue) : CircuitMaskSample :=
  circuitMaskSourceFromSelected (sample.retargetMask input curveTarget (Vector.ofFn targets)) mask rows input

/-- The selected-source inverse recovers every original mask-source field. -/
theorem circuitMaskSourceFromSelected_garble (bridgeKey mask : BaseField)
    (rows : FieldMacToECMac.Rows) (input : AffineInput) (source : CircuitMaskSample) :
    circuitMaskSourceFromSelected (circuitMaskSampleGarble bridgeKey mask rows input source)
      mask (fun row => rows.get row) input = source := by
  apply Prod.ext
  · apply Prod.ext
    · change (curveMaskShiftEquiv mask input).symm (curveMaskShiftEquiv mask input source.1.1) = source.1.1
      exact (curveMaskShiftEquiv mask input).symm_apply_apply source.1.1
    · rfl
  · funext row
    change _ = source.2 row
    simp only [circuitMaskSourceFromSelected, circuitMaskSampleGarble, Vector.get_ofFn]
    apply Prod.ext
    · apply Prod.ext
      · change (xMaskSelectedEquiv ![(rows.get row).x.x, (rows.get row).x.y,
          (rows.get row).x.xy, (rows.get row).x.ySquared] input).symm
          ((xMaskSelectedEquiv ![(rows.get row).x.x, (rows.get row).x.y,
            (rows.get row).x.xy, (rows.get row).x.ySquared] input) (source.2 row).1.1) = (source.2 row).1.1
        exact Equiv.symm_apply_apply _ _
      · rfl
    · apply Prod.ext
      · apply Prod.ext
        · change (yMaskSelectedEquiv ![(rows.get row).y.x, (rows.get row).y.xSquared,
            (rows.get row).y.ySquared] input).symm
            ((yMaskSelectedEquiv ![(rows.get row).y.x, (rows.get row).y.xSquared,
              (rows.get row).y.ySquared] input) (source.2 row).2.1.1) = (source.2 row).2.1.1
          exact Equiv.symm_apply_apply _ _
        · rfl
      · apply Prod.ext
        · change (zMaskSelectedEquiv ![(rows.get row).z.y, (rows.get row).z.xy,
            (rows.get row).z.xSquared, (rows.get row).z.ySquared] input).symm
            ((zMaskSelectedEquiv ![(rows.get row).z.y, (rows.get row).z.xy,
              (rows.get row).z.xSquared, (rows.get row).z.ySquared] input) (source.2 row).2.2.1) = (source.2 row).2.2.1
          exact Equiv.symm_apply_apply _ _
        · rfl

private theorem vector_ofFn_get {Value : Type*} {count : Nat} (values : Vector Value count) :
    Vector.ofFn (fun row => values.get row) = values := by
  apply Vector.ext
  intro index inRange
  simp only [Vector.getElem_ofFn]
  rfl

/-- The reconstructed source is exactly the source of the circuit mask split. -/
theorem reconstructedCircuitSource_eq_split (bridgeKey mask : BaseField)
    (rows : FieldMacToECMac.Rows) (sparse : ∀ row, FieldMacToECMac.SparseRow (rows.get row))
    (input : AffineInput) (sample : PublicSample) :
    reconstructedCircuitSource sample mask (fun row => rows.get row) input
      (bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2))
      (fun row => (FieldMacToECMac.evaluateRowsCubic rows input).get row) =
        (circuitMaskSampleSplit bridgeKey mask rows input sample).2 := by
  have law := congrArg (fun selected => circuitMaskSourceFromSelected selected mask
    (fun row => rows.get row) input) (circuitMaskSampleGarble_split bridgeKey mask rows sparse input sample)
  rw [circuitMaskSourceFromSelected_garble] at law
  have targets : Vector.ofFn (fun row => (FieldMacToECMac.evaluateRowsCubic rows input).get row) =
      FieldMacToECMac.evaluateRowsCubic rows input := vector_ofFn_get _
  unfold reconstructedCircuitSource
  rw [targets]
  exact law.symm


private theorem xBranchSlope_source (sample : XPublicSample) (coefficients : Fin 4 → BaseField)
    (input : AffineInput) (target : BaseField) (gate : Fin 4) :
    sample.branchSlope coefficients input gate =
      let source := (xMaskSelectedEquiv coefficients input).symm
        ((fun index => sample.coefficients index.succ), (sample.retargetMask input target).targets)
      ![-source.1 2, -source.1 3, -(source.1 1 + DigitAdaptor.fromBits (source.2 1)),
        -(source.1 0 + DigitAdaptor.fromBits (source.2 0))] gate := by
  fin_cases gate <;>
    dsimp only [xMaskSelectedEquiv, Equiv.coe_fn_symm_mk, Equiv.symm, Equiv.coe_fn_mk, XPublicSample.branchSlope, maskShiftEquiv]
  all_goals simp [XPublicSample.retargetMask]

private theorem yBranchSlope_source (sample : YPublicSample) (coefficients : Fin 3 → BaseField)
    (input : AffineInput) (target : BaseField) (gate : Fin 3) :
    sample.branchSlope coefficients input gate =
      let source := (yMaskSelectedEquiv coefficients input).symm
        ((fun index => sample.coefficients index.succ), (sample.retargetMask input target).targets)
      ![-source.1 2, -(source.1 1 + DigitAdaptor.fromBits (source.2 0)),
        -(source.1 0 + DigitAdaptor.fromBits (source.2 1))] gate := by
  fin_cases gate <;>
    dsimp only [yMaskSelectedEquiv, Equiv.coe_fn_symm_mk, Equiv.symm, Equiv.coe_fn_mk, YPublicSample.branchSlope, maskShiftEquiv]
  all_goals simp [YPublicSample.retargetMask]

private theorem zBranchSlope_source (sample : ZPublicSample) (coefficients : Fin 4 → BaseField)
    (input : AffineInput) (target : BaseField) (gate : Fin 5) :
    sample.branchSlope coefficients input gate =
      let source := (zMaskSelectedEquiv coefficients input).symm
        ((fun index => sample.coefficients index.succ), (sample.retargetMask input target).targets)
      ![-source.1 1, -source.1 3, -(source.1 0 + DigitAdaptor.fromBits (source.2 1)),
        -source.1 2, -(DigitAdaptor.fromBits (source.2 0) + DigitAdaptor.fromBits (source.2 3))] gate := by
  fin_cases gate <;>
    dsimp only [zMaskSelectedEquiv, Equiv.coe_fn_symm_mk, Equiv.symm, Equiv.coe_fn_mk, ZPublicSample.branchSlope, maskShiftEquiv]
  all_goals simp [ZPublicSample.retargetMask]

def pointRawGate (row : Fin FieldMacToECMac.outputMacCount)
    (family : PointGateFamily) (bit : Fin coordinateBitCount) : RawCircuitGate :=
  match family with
  | .inl gate => .inr (row, .inl (gate, bit))
  | .inr (.inl gate) => .inr (row, .inr (.inl (gate, bit)))
  | .inr (.inr gate) => .inr (row, .inr (.inr (gate, bit)))

private theorem retargetPoint (sample : PublicSample) (input : AffineInput)
    (curveTarget : BaseField) (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (row : Fin FieldMacToECMac.outputMacCount) :
    ((sample.retargetMask input curveTarget (Vector.ofFn targets)).points.get row) =
      (sample.points.get row).retargetMask input (targets row) := by
  simp only [PublicSample.retargetMask, Vector.get_ofFn]

theorem reconstructedCircuitSource_pointField (sample : PublicSample) (mask : BaseField)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows) (input : AffineInput)
    (curveTarget : BaseField)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (row : Fin FieldMacToECMac.outputMacCount) (family : PointGateFamily)
    (bit : Fin coordinateBitCount) :
    circuitSourceField (reconstructedCircuitSource sample mask rows input curveTarget targets)
      (pointRawGate row family bit) =
      ((sample.points.get row).branchTargetQuotient (rows row) input (targets row) family bit false).1 := by
  rcases family with gate | (gate | gate) <;>
    simp only [pointRawGate, circuitSourceField, reconstructedCircuitSource,
      circuitMaskSourceFromSelected, retargetPoint, RowPublicSample.retargetMask,
      RowPublicSample.branchTargetQuotient]
  · exact (XPublicSample.branchTarget_false_source (sample.points.get row).x
      ![(rows row).x.x, (rows row).x.y, (rows row).x.xy, (rows row).x.ySquared]
      input (targets row).x gate bit).symm
  · exact (YPublicSample.branchTarget_false_source (sample.points.get row).y
      ![(rows row).y.x, (rows row).y.xSquared, (rows row).y.ySquared]
      input (targets row).y gate bit).symm
  · exact (ZPublicSample.branchTarget_false_source (sample.points.get row).z
      ![(rows row).z.y, (rows row).z.xy, (rows row).z.xSquared, (rows row).z.ySquared]
      input (targets row).z gate bit).symm

theorem reconstructedCircuitSource_pointTarget (sample : PublicSample) (mask : BaseField)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows) (input : AffineInput)
    (curveTarget : BaseField)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (row : Fin FieldMacToECMac.outputMacCount) (family : PointGateFamily)
    (bit : Fin coordinateBitCount) :
    circuitSourceSlope (reconstructedCircuitSource sample mask rows input curveTarget targets)
      (pointRawGate row family bit) +
      circuitSourceField (reconstructedCircuitSource sample mask rows input curveTarget targets)
        (pointRawGate row family bit) =
      ((sample.points.get row).branchTargetQuotient (rows row) input (targets row) family bit true).1 := by
  rw [reconstructedCircuitSource_pointField]
  rcases family with gate | (gate | gate) <;>
    simp only [pointRawGate, circuitSourceSlope, reconstructedCircuitSource,
      circuitMaskSourceFromSelected, retargetPoint, RowPublicSample.retargetMask,
      RowPublicSample.branchTargetQuotient]
  · rw [XPublicSample.branchTarget_true, xBranchSlope_source (sample.points.get row).x
      ![(rows row).x.x, (rows row).x.y, (rows row).x.xy, (rows row).x.ySquared] input (targets row).x gate]
    exact add_comm _ _
  · rw [YPublicSample.branchTarget_true, yBranchSlope_source (sample.points.get row).y
      ![(rows row).y.x, (rows row).y.xSquared, (rows row).y.ySquared] input (targets row).y gate]
    exact add_comm _ _
  · rw [ZPublicSample.branchTarget_true, zBranchSlope_source (sample.points.get row).z
      ![(rows row).z.y, (rows row).z.xy, (rows row).z.xSquared, (rows row).z.ySquared] input (targets row).z gate]
    exact add_comm _ _

theorem reconstructedCircuitSource_pointPair (sample : PublicSample) (mask : BaseField)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows) (input : AffineInput)
    (curveTarget : BaseField)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (row : Fin FieldMacToECMac.outputMacCount) (family : PointGateFamily)
    (bit : Fin coordinateBitCount) :
    (circuitMaskHashSplitEquiv (reconstructedCircuitSource sample mask rows input curveTarget targets)).1
      (pointRawGate row family bit) =
      ((sample.points.get row).branchTargetQuotient (rows row) input (targets row) family bit false) := by
  apply Prod.ext
  · rw [circuitMaskHashSplit_field]
    exact reconstructedCircuitSource_pointField sample mask rows input curveTarget targets row family bit
  · rcases family with gate | (gate | gate) <;>
      simp only [pointRawGate, circuitMaskHashSplitEquiv, maskHashSplitEquiv,
        reconstructedCircuitSource, circuitMaskSourceFromSelected, retargetPoint,
        RowPublicSample.retargetMask, RowPublicSample.branchTargetQuotient] <;> rfl


theorem reconstructedCircuitSource_pointOffset (sample : PublicSample) (mask : BaseField)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows) (input : AffineInput)
    (curveTarget : BaseField)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (row : Fin FieldMacToECMac.outputMacCount) (family : PointGateFamily)
    (bit : Fin coordinateBitCount) (slot : Pipeline.FixedKeySlot) :
    let source := reconstructedCircuitSource sample mask rows input curveTarget targets
    circuitSourceOffset source (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
      (pointRawGate row family bit) slot =
      pointBranchBlock (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).1
        (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).2
        (rows row) input (targets row) family bit slot := by
  dsimp only
  cases slot with
  | hash index =>
      simp only [circuitSourceOffset, goodHashLiftSource_blocks, pointBranchBlock,
        Prod.mk.eta, Equiv.symm_apply_apply]
      rw [reconstructedCircuitSource_pointPair]
      congr 3
  | pad index =>
      simp only [circuitSourceOffset, goodHashLiftSource_field, circuitMaskHashSplit_field,
        pointBranchBlock, Prod.mk.eta, Equiv.symm_apply_apply]
      rw [reconstructedCircuitSource_pointTarget]
      congr 1
      rcases family with gate | (gate | gate) <;>
        simp only [pointRawGate, circuitSourceTable, reconstructedCircuitSource,
          circuitMaskSourceFromSelected, retargetPoint, RowPublicSample.retargetMask,
          VisibleRowSample.gateTable, RowPublicSample.visibleHiddenEquiv,
          XPublicSample.visibleHiddenEquiv, YPublicSample.visibleHiddenEquiv,
          ZPublicSample.visibleHiddenEquiv] <;> rfl

/-- The point collision flag excludes every repeated reconstructed point offset. -/
theorem reconstructedCircuitSource_pointOffset_injective (sample : PublicSample) (mask : BaseField)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows) (input : AffineInput)
    (curveTarget : BaseField)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (good : ¬ pointBranchCollision
      (fun row => (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).1)
      rows input targets
      (fun row => (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).2))
    (family : PointGateFamily) (bit : Fin coordinateBitCount) (slot : Pipeline.FixedKeySlot) :
    let source := reconstructedCircuitSource sample mask rows input curveTarget targets
    Function.Injective (fun row => circuitSourceOffset source
      (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
      (pointRawGate row family bit) slot) := by
  dsimp only
  simp_rw [reconstructedCircuitSource_pointOffset]
  exact pointBranchCollision_false_injective _ rows input targets _ good family bit slot

theorem reconstructedCircuitSource_bucketOffset_injective (sample : PublicSample) (mask : BaseField)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows) (input : AffineInput)
    (curveTarget : BaseField)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (good : ¬ pointBranchCollision
      (fun row => (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).1)
      rows input targets
      (fun row => (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).2))
    (index : Pipeline.FixedKeyIndex) :
    let source := reconstructedCircuitSource sample mask rows input curveTarget targets
    Function.Injective (fun row => circuitSourceOffset source
      (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
      (circuitBucketGate index row) index.slot) := by
  dsimp only
  rcases index with ⟨kind, bit, slot⟩
  cases kind with
  | curve adaptor =>
      intro first second _
      exact @Subsingleton.elim (Fin 1) inferInstance first second
  | point coordinate adaptor =>
      cases coordinate <;> cases adaptor <;>
        try { intro first; exact Fin.elim0 first }
      all_goals dsimp only [circuitBucketGate]
      · exact reconstructedCircuitSource_pointOffset_injective sample mask rows input curveTarget targets good (.inl 0) bit slot
      · exact reconstructedCircuitSource_pointOffset_injective sample mask rows input curveTarget targets good (.inl 1) bit slot
      · exact reconstructedCircuitSource_pointOffset_injective sample mask rows input curveTarget targets good (.inl 2) bit slot
      · exact reconstructedCircuitSource_pointOffset_injective sample mask rows input curveTarget targets good (.inl 3) bit slot
      · exact reconstructedCircuitSource_pointOffset_injective sample mask rows input curveTarget targets good (.inr (.inl 0)) bit slot
      · exact reconstructedCircuitSource_pointOffset_injective sample mask rows input curveTarget targets good (.inr (.inl 1)) bit slot
      · exact reconstructedCircuitSource_pointOffset_injective sample mask rows input curveTarget targets good (.inr (.inl 2)) bit slot
      · exact reconstructedCircuitSource_pointOffset_injective sample mask rows input curveTarget targets good (.inr (.inr 0)) bit slot
      · exact reconstructedCircuitSource_pointOffset_injective sample mask rows input curveTarget targets good (.inr (.inr 1)) bit slot
      · exact reconstructedCircuitSource_pointOffset_injective sample mask rows input curveTarget targets good (.inr (.inr 2)) bit slot
      · exact reconstructedCircuitSource_pointOffset_injective sample mask rows input curveTarget targets good (.inr (.inr 3)) bit slot
      · exact reconstructedCircuitSource_pointOffset_injective sample mask rows input curveTarget targets good (.inr (.inr 4)) bit slot

theorem reconstructedCircuitSource_rawOffset_injective (sample : PublicSample) (mask : BaseField)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows) (input : AffineInput)
    (curveTarget : BaseField)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (good : ¬ pointBranchCollision
      (fun row => (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).1)
      rows input targets
      (fun row => (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).2))
    (pointKey curveKey : InputMacKey) (index : Pipeline.FixedKeyIndex) :
    let source := reconstructedCircuitSource sample mask rows input curveTarget targets
    Function.Injective (rawBucketOffset (sourceGatePrescription source pointKey curveKey
      (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))) index) := by
  dsimp only
  let source := reconstructedCircuitSource sample mask rows input curveTarget targets
  let keys := circuitGateKey pointKey curveKey
  let lifts := fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)
  intro first second equal
  obtain ⟨firstRow, rfl⟩ := circuitBucketUse_surjective keys (circuitSourceSlope source) lifts
    (circuitSourceTable source) index first
  obtain ⟨secondRow, rfl⟩ := circuitBucketUse_surjective keys (circuitSourceSlope source) lifts
    (circuitSourceTable source) index second
  apply congrArg
  apply reconstructedCircuitSource_bucketOffset_injective sample mask rows input curveTarget targets good index
  exact equal

/-- Both checked flags make the reconstructed source schedule fresh. -/
theorem reconstructedCircuitSource_schedule_fresh
    (state : SimulatorState) (oracle : SimulatorOracleCoin) (bridgeKey mask : BaseField)
    (sample : PublicSample) (rows : FieldMacToECMac.Rows) (input : AffineInput)
    (curveTarget : BaseField)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (key : InputMacKey)
    (pointGood : ¬ pointBranchCollision
      (fun row => (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).1)
      (fun row => rows.get row) input targets
      (fun row => (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).2))
    (prefixGood : let source := reconstructedCircuitSource sample mask (fun row => rows.get row) input curveTarget targets
      ¬ prequeryLabelCollision state.fixedTranscript
        (sourcePrequeryLabelUses oracle bridgeKey source
          (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
          state.fixedTranscript) key) :
    let source := reconstructedCircuitSource sample mask (fun row => rows.get row) input curveTarget targets
    let pointKey := EncPRF.transformKey oracle.encOracle (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key
    let garbled :=  circuitMaskSampleGarble bridgeKey mask rows input source
    FreshRecordSchedule state.fixedTranscript (gateProgramRecords
      (pipelineGateSchedule garbled.curveRequest garbled.pointRequests input
        (key.encodeAffine input) (pointKey.encodeAffine input))) := by
  dsimp only
  apply circuitMaskSchedule_fresh
  · exact reconstructedCircuitSource_rawOffset_injective sample mask (fun row => rows.get row)
      input curveTarget targets pointGood _ key
  · intro gate slot _
    exact sourcePrequeryLabelCollision_false_fresh oracle bridgeKey _ _ state.fixedTranscript key prefixGood gate slot

end Kriterion.ArgoMAC.Security
