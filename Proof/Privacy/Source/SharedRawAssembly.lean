import Proof.Privacy.Source.SharedRetainedSource
import Proof.Privacy.Source.SharedBucketCounts

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 2048

/-- The public slot and branch together identify one internal role. -/
theorem sharedRole_injective : Function.Injective
    (fun role : Pipeline.FixedKeySlot => (Shared.slotIndex role, rawSlotBranch role)) := by
  intro first second equal
  have slots := congrArg Prod.fst equal
  have branches := congrArg Prod.snd equal
  cases first with
  | hash first => cases second with
    | hash second => exact congrArg Pipeline.FixedKeySlot.hash slots
    | pad second => cases branches
  | pad first => cases second with
    | hash second => cases branches
    | pad second =>
      apply congrArg Pipeline.FixedKeySlot.pad
      exact Fin.ext (congrArg (fun index : Fin 3 => index.val) slots)

/-- This index lists the hidden branch before the selected branch. -/
def sharedRoleRow {Row : Type} (selected : Bool) (pair : Pipeline.FixedKeySlot × Row) : Row ⊕ Row :=
  if rawSlotBranch pair.1 = selected then .inr pair.2 else .inl pair.2

/-- The branch index has no repetitions within one actual public slot. -/
theorem sharedRoleRow_injective {Row : Type} (slot : Fin 3) (selected : Bool) :
    Function.Injective (fun pair : SharedSlotRole slot × Row => sharedRoleRow selected (pair.1.1, pair.2)) := by
  rintro ⟨first, row1⟩ ⟨second, row2⟩ equal
  have branch : rawSlotBranch first.1 = rawSlotBranch second.1 := by
    cases selected <;> cases firstBit : rawSlotBranch first.1 <;>
      cases secondBit : rawSlotBranch second.1 <;> simp_all [sharedRoleRow]
  have roles : first = second := by
    apply Subtype.ext
    apply sharedRole_injective
    exact Prod.ext (first.2.trans second.2.symm) branch
  subst second
  apply congrArg (fun row => (first, row))
  by_cases active : rawSlotBranch first.1 = selected <;>
    simpa only [sharedRoleRow, active, if_true, if_false, Sum.inl.injEq, Sum.inr.injEq] using equal

/-- A shared role equals the hash or pad role of that public slot. -/
theorem sharedRole_eq (slot : Fin 2) (role : SharedSlotRole slot.castSucc) :
    role.1 = sharedBranchRole (rawSlotBranch role.1) slot := by
  rcases role with ⟨role, equal⟩
  cases role with
  | hash index =>
      change index = slot.castSucc at equal
      subst index
      rfl
  | pad index =>
      have same : index = slot := Fin.ext (congrArg (fun index : Fin 3 => index.val) equal)
      subst index
      rfl

/-- The point family selects the same label wire at every digit row. -/
theorem pointRawGate_wire (row : Fin FieldMacToECMac.outputMacCount)
    (family : PointGateFamily) (position : Fin coordinateBitCount) :
    circuitGateWire (pointRawGate row family position) = (family.coordinate, position) := by
  rcases family with gate | (gate | gate) <;> fin_cases gate <;> rfl


/-- This equivalence lists the actual role and row of each shared bucket use. -/
def sharedCircuitBucketListEquiv
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (index : Shared.FixedKeyIndex) :
    SharedRawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index ≃
      SharedSlotRole index.slot × Fin (circuitBucketSize ⟨index.kind, index.position, .hash 0⟩) :=
  (sharedRawBucketRoleEquiv _ index).trans (Equiv.sigmaEquivProdOfEquiv fun role =>
    (circuitBucketUseEquiv keys slopes lifts tables ⟨index.kind, index.position, role.1⟩).symm)

/-- The bucket enumeration retains the exact raw gate and role. -/
theorem sharedCircuitBucketListEquiv_gate
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (index : Shared.FixedKeyIndex)
    (entry : SharedSlotRole index.slot × Fin (circuitBucketSize ⟨index.kind, index.position, .hash 0⟩)) :
    ((sharedCircuitBucketListEquiv keys slopes lifts tables index).symm entry).1 =
      (circuitBucketGate ⟨index.kind, index.position, entry.1.1⟩ entry.2, entry.1.1) := rfl



/-- The last public slot contains only its hash role. -/
theorem sharedLastRole (role : SharedSlotRole 2) : role.1 = .hash 2 := by
  rcases role with ⟨role, equal⟩
  cases role with
  | hash index => exact congrArg Pipeline.FixedKeySlot.hash equal
  | pad index =>
      have numeric := congrArg (fun value : Fin 3 => value.val) equal
      have bound := index.isLt
      change index.val = 2 at numeric
      omega

private instance sharedLastRoleSubsingleton : Subsingleton (SharedSlotRole 2) :=
  ⟨fun first second => Subtype.ext ((sharedLastRole first).trans (sharedLastRole second).symm)⟩


namespace SharedRetained

/-- The retained source fixes the selected label and keeps its unused partner. -/
def Context.gateLabel (context : Context) (labels : EncPRF.PermutationIndex → Block)
    (gate : RawCircuitGate) (branch : Bool) : Block :=
  let index := circuitGateWire gate
  let active := branch = inputSelectedLabelBit context.input index
  match gate with
  | .inl _ => if active then context.activeCurveLabels index else labels index
  | .inr _ => if active then context.activePointLabels index else labels index ^^^ context.hiddenPointPads index

/-- These actual raw prescriptions use the retained source masks, ciphertexts, and labels. -/
def Context.gates (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block)) : RawCircuitGate → RawGatePrescription :=
  circuitRawGatePrescription
    (fun gate => ⟨context.gateLabel sample.2 gate false, context.gateLabel sample.2 gate true⟩)
    (circuitSourceSlope (context.source sample.1)) (context.lifts sample.1)
    (circuitSourceTable (context.source sample.1))

/-- A point label is constant across every digit row in its bucket. -/
theorem point_gateLabel (context : Context) (labels : EncPRF.PermutationIndex → Block)
    (row : Fin FieldMacToECMac.outputMacCount) (family : PointGateFamily)
    (position : Fin coordinateBitCount) (branch : Bool) :
    context.gateLabel labels (pointRawGate row family position) branch =
      if branch = family.selectedBit context.input position then
        context.activePointLabels (family.coordinate, position)
      else labels (family.coordinate, position) ^^^ context.hiddenPointPads (family.coordinate, position) := by
  unfold Context.gateLabel
  rw [pointRawGate_wire]
  dsimp only
  rw [← PointGateFamily.selectedBit_coordinate]
  rcases family with gate | (gate | gate) <;> rfl

/-- Each retained raw label is the label of its actual hash or pad branch. -/
theorem raw_gate_label (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot) :
    (context.gates sample gate).label slot = context.gateLabel sample.2 gate (rawSlotBranch slot) := by
  cases slot <;> rfl

/-- Each retained raw range uses the same actual source offset. -/
theorem raw_gate_offset (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot) :
    (context.gates sample gate).offset slot =
      circuitSourceOffset (context.source sample.1) (context.lifts sample.1) gate slot := by
  cases slot <;> rfl


/-- The raw point domain uses its retained branch label and exact digit tweak. -/
theorem point_raw_domain (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (row : Fin FieldMacToECMac.outputMacCount) (family : PointGateFamily)
    (position : Fin coordinateBitCount) (role : Pipeline.FixedKeySlot) :
    ((context.gates sample (pointRawGate row family position)).slotRecord role).domain =
      (if rawSlotBranch role = family.selectedBit context.input position then
        context.activePointLabels (family.coordinate, position)
      else sample.2 (family.coordinate, position) ^^^ context.hiddenPointPads (family.coordinate, position)) ^^^
        BitVec.ofNat 128 row.val := by
  change gateInput (rawCircuitLocation (pointRawGate row family position))
    ((context.gates sample (pointRawGate row family position)).label role) = _
  rw [raw_gate_label, point_gateLabel]
  rcases family with gate | (gate | gate) <;> rfl

/-- The raw point range uses its retained branch label and the same source offset. -/
theorem point_raw_range (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (row : Fin FieldMacToECMac.outputMacCount) (family : PointGateFamily)
    (position : Fin coordinateBitCount) (role : Pipeline.FixedKeySlot) :
    ((context.gates sample (pointRawGate row family position)).slotRecord role).range =
      pointBranchOffset row (context.visible.2 row) (sample.1.2 row) (context.rows row)
        context.input (context.targets row) family position role ^^^
      (if rawSlotBranch role = family.selectedBit context.input position then
        context.activePointLabels (family.coordinate, position)
      else sample.2 (family.coordinate, position) ^^^ context.hiddenPointPads (family.coordinate, position)) := by
  change (context.gates sample (pointRawGate row family position)).offset role ^^^
    gateInput (rawCircuitLocation (pointRawGate row family position))
      ((context.gates sample (pointRawGate row family position)).label role) = _
  rw [raw_gate_offset, raw_gate_label, point_gateLabel, ← point_source_offset]
  simp only [gateInput]
  ac_rfl

/-- This function lists each retained point domain through its hidden or selected branch. -/
theorem point_domain_branch (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (family : PointGateFamily) (position : Fin coordinateBitCount) (slot : Fin 2)
    (entry : SharedSlotRole slot.castSucc × Fin FieldMacToECMac.outputMacCount) :
    ((context.gates sample (pointRawGate entry.2 family position)).slotRecord entry.1.1).domain =
      Sum.elim
        (fun row : Fin FieldMacToECMac.outputMacCount => (sample.2 (family.coordinate, position) ^^^
          context.hiddenPointPads (family.coordinate, position)) ^^^ BitVec.ofNat 128 row.val)
        (fun row : Fin FieldMacToECMac.outputMacCount => context.activePointLabels (family.coordinate, position) ^^^ BitVec.ofNat 128 row.val)
        (sharedRoleRow (family.selectedBit context.input position) (entry.1.1, entry.2)) := by
  rw [point_raw_domain]
  unfold sharedRoleRow
  split <;> rfl

/-- This function lists each retained point range through its actual grouped source offset. -/
theorem point_range_branch (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (family : PointGateFamily) (position : Fin coordinateBitCount) (slot : Fin 2)
    (entry : SharedSlotRole slot.castSucc × Fin FieldMacToECMac.outputMacCount) :
    let branches := context.pointBranches sample.1 (family.coordinate, position)
    let groupSlot := pointFamilySlotEquiv family.coordinate (⟨family, rfl⟩, slot)
    ((context.gates sample (pointRawGate entry.2 family position)).slotRecord entry.1.1).range =
      Sum.elim
        (fun row => branches.hiddenOffset groupSlot row ^^^
          (sample.2 (family.coordinate, position) ^^^ context.hiddenPointPads (family.coordinate, position)))
        (fun row => branches.activeOffset groupSlot row ^^^ context.activePointLabels (family.coordinate, position))
        (sharedRoleRow (family.selectedBit context.input position) (entry.1.1, entry.2)) := by
  dsimp only
  rw [point_raw_range]
  have role := sharedRole_eq slot entry.1
  by_cases active : rawSlotBranch entry.1.1 = family.selectedBit context.input position
  · simp only [sharedRoleRow, active, if_true, Sum.elim_inr, Context.pointBranches]
    rw [pointSharedBranches_activeOffset, role, active]
  · have hidden : rawSlotBranch entry.1.1 = !(family.selectedBit context.input position) := by
      exact Bool.eq_not_iff.mpr active
    simp only [sharedRoleRow, active, if_false, Sum.elim_inl, Context.pointBranches]
    rw [pointSharedBranches_hiddenOffset, role, hidden]

/-- Good retained data makes every actual point role-row assignment injective. -/
theorem point_role_assignments_injective (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (good : ¬ context.collision sample) (family : PointGateFamily)
    (position : Fin coordinateBitCount) (slot : Fin 2) :
    Function.Injective (fun entry : SharedSlotRole slot.castSucc × Fin FieldMacToECMac.outputMacCount =>
      ((context.gates sample (pointRawGate entry.2 family position)).slotRecord entry.1.1).domain) ∧
    Function.Injective (fun entry : SharedSlotRole slot.castSucc × Fin FieldMacToECMac.outputMacCount =>
      ((context.gates sample (pointRawGate entry.2 family position)).slotRecord entry.1.1).range) := by
  have branches := point_assignments_injective context sample good (family.coordinate, position)
    (pointFamilySlotEquiv family.coordinate (⟨family, rfl⟩, slot))
  have rows := sharedRoleRow_injective (Row := Fin FieldMacToECMac.outputMacCount) slot.castSucc (family.selectedBit context.input position)
  constructor
  · intro first second equal
    apply rows
    apply branches.1
    simpa only [point_domain_branch, Context.pointBranches, pointSharedBranches] using equal
  · intro first second equal
    apply rows
    apply branches.2
    simpa only [point_range_branch] using equal


/-- A curve label is the selected label or its retained unused partner. -/
theorem curve_gateLabel (context : Context) (labels : EncPRF.PermutationIndex → Block)
    (family : Fin 5) (position : Fin coordinateBitCount) (branch : Bool) :
    context.gateLabel labels (.inl (family, position)) branch =
      if branch = inputSelectedLabelBit context.input (curveSharedCoordinate family, position) then
        context.activeCurveLabels (curveSharedCoordinate family, position)
      else labels (curveSharedCoordinate family, position) := by
  unfold Context.gateLabel
  rw [curveSharedCoordinate_wire]

/-- The raw curve domain uses its retained branch label and the paper curve tweak. -/
theorem curve_raw_domain (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (family : Fin 5) (position : Fin coordinateBitCount) (role : Pipeline.FixedKeySlot) :
    ((context.gates sample (.inl (family, position))).slotRecord role).domain =
      (if rawSlotBranch role = inputSelectedLabelBit context.input (curveSharedCoordinate family, position) then
        context.activeCurveLabels (curveSharedCoordinate family, position)
      else sample.2 (curveSharedCoordinate family, position)) ^^^ BitVec.ofNat 128 FieldMacToECMac.outputMacCount := by
  change gateInput (rawCircuitLocation (.inl (family, position)))
    ((context.gates sample (.inl (family, position))).label role) = _
  rw [raw_gate_label, curve_gateLabel]
  simp only [gateInput, curveSharedTweak]

/-- The raw curve range uses the same retained source offset as the grouped proof. -/
theorem curve_raw_range (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (family : Fin 5) (position : Fin coordinateBitCount) (role : Pipeline.FixedKeySlot) :
    ((context.gates sample (.inl (family, position))).slotRecord role).range =
      (circuitSourceOffset (context.source sample.1) (context.lifts sample.1) (.inl (family, position)) role ^^^
        BitVec.ofNat 128 FieldMacToECMac.outputMacCount) ^^^
      (if rawSlotBranch role = inputSelectedLabelBit context.input (curveSharedCoordinate family, position) then
        context.activeCurveLabels (curveSharedCoordinate family, position)
      else sample.2 (curveSharedCoordinate family, position)) := by
  change (context.gates sample (.inl (family, position))).offset role ^^^
    gateInput (rawCircuitLocation (.inl (family, position)))
      ((context.gates sample (.inl (family, position))).label role) = _
  rw [raw_gate_offset, raw_gate_label, curve_gateLabel]
  simp only [gateInput, curveSharedTweak]
  ac_rfl

/-- Each curve domain occurs at its exact hidden or selected branch position. -/
theorem curve_domain_branch (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (family : Fin 5) (position : Fin coordinateBitCount) (slot : Fin 2)
    (entry : SharedSlotRole slot.castSucc × Fin 1) :
    ((context.gates sample (.inl (family, position))).slotRecord entry.1.1).domain =
      Sum.elim
        (fun _row : Fin 1 => sample.2 (curveSharedCoordinate family, position) ^^^ BitVec.ofNat 128 FieldMacToECMac.outputMacCount)
        (fun _row : Fin 1 => context.activeCurveLabels (curveSharedCoordinate family, position) ^^^ BitVec.ofNat 128 FieldMacToECMac.outputMacCount)
        (sharedRoleRow (inputSelectedLabelBit context.input (curveSharedCoordinate family, position))
          (entry.1.1, entry.2)) := by
  rw [curve_raw_domain]
  unfold sharedRoleRow
  split <;> rfl

/-- Each curve range occurs at its exact grouped source offset. -/
theorem curve_range_branch (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (family : Fin 5) (position : Fin coordinateBitCount) (slot : Fin 2)
    (entry : SharedSlotRole slot.castSucc × Fin 1) :
    let branches := context.curveBranches sample.1 (curveSharedCoordinate family, position)
    let groupSlot := curveFamilySlotEquiv (curveSharedCoordinate family) (⟨family, rfl⟩, slot)
    ((context.gates sample (.inl (family, position))).slotRecord entry.1.1).range =
      Sum.elim
        (fun row => branches.hiddenOffset groupSlot row ^^^ sample.2 (curveSharedCoordinate family, position))
        (fun row => branches.activeOffset groupSlot row ^^^ context.activeCurveLabels (curveSharedCoordinate family, position))
        (sharedRoleRow (inputSelectedLabelBit context.input (curveSharedCoordinate family, position))
          (entry.1.1, entry.2)) := by
  dsimp only
  rw [curve_raw_range]
  have role := sharedRole_eq slot entry.1
  by_cases active : rawSlotBranch entry.1.1 =
      inputSelectedLabelBit context.input (curveSharedCoordinate family, position)
  · simp only [sharedRoleRow, active, if_true, Sum.elim_inr, Context.curveBranches]
    rw [curveSharedBranches_activeOffset, curveSharedCoordinate_wire, curveSharedTweak, role, active]
  · have hidden : rawSlotBranch entry.1.1 =
        !(inputSelectedLabelBit context.input (curveSharedCoordinate family, position)) := Bool.eq_not_iff.mpr active
    simp only [sharedRoleRow, active, if_false, Sum.elim_inl, Context.curveBranches]
    rw [curveSharedBranches_hiddenOffset, curveSharedCoordinate_wire, curveSharedTweak, role, hidden]

/-- Good retained data makes every actual curve role-row assignment injective. -/
theorem curve_role_assignments_injective (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (good : ¬ context.collision sample) (family : Fin 5)
    (position : Fin coordinateBitCount) (slot : Fin 2) :
    Function.Injective (fun entry : SharedSlotRole slot.castSucc × Fin 1 =>
      ((context.gates sample (.inl (family, position))).slotRecord entry.1.1).domain) ∧
    Function.Injective (fun entry : SharedSlotRole slot.castSucc × Fin 1 =>
      ((context.gates sample (.inl (family, position))).slotRecord entry.1.1).range) := by
  have branches := curve_assignments_injective context sample good (curveSharedCoordinate family, position)
    (curveFamilySlotEquiv (curveSharedCoordinate family) (⟨family, rfl⟩, slot))
  have rows := sharedRoleRow_injective (Row := Fin 1) slot.castSucc
    (inputSelectedLabelBit context.input (curveSharedCoordinate family, position))
  constructor
  · intro first second equal
    apply rows
    apply branches.1
    simpa only [curve_domain_branch, Context.curveBranches, curveSharedBranches] using equal
  · intro first second equal
    apply rows
    apply branches.2
    simpa only [curve_range_branch] using equal


/-- This equivalence lists every role-row pair of a retained raw bucket. -/
def Context.bucketEquiv (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block)) (index : Shared.FixedKeyIndex) :
    SharedRawBucketUse (context.gates sample) index ≃
      SharedSlotRole index.slot × Fin (circuitBucketSize ⟨index.kind, index.position, .hash 0⟩) :=
  sharedCircuitBucketListEquiv _ _ _ _ index

/-- The listed domain equals its actual raw gate domain. -/
theorem bucket_domain_listed (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block)) (index : Shared.FixedKeyIndex)
    (entry : SharedSlotRole index.slot × Fin (circuitBucketSize ⟨index.kind, index.position, .hash 0⟩)) :
    sharedRawBucketDomain (context.gates sample) index ((context.bucketEquiv sample index).symm entry) =
      ((context.gates sample (circuitBucketGate ⟨index.kind, index.position, entry.1.1⟩ entry.2)).slotRecord
        entry.1.1).domain := rfl

/-- The listed range equals its actual raw gate range. -/
theorem bucket_range_listed (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block)) (index : Shared.FixedKeyIndex)
    (entry : SharedSlotRole index.slot × Fin (circuitBucketSize ⟨index.kind, index.position, .hash 0⟩)) :
    sharedRawBucketRange (context.gates sample) index ((context.bucketEquiv sample index).symm entry) =
      ((context.gates sample (circuitBucketGate ⟨index.kind, index.position, entry.1.1⟩ entry.2)).slotRecord
        entry.1.1).range := rfl

/-- Good retained data gives distinct listed assignments in the two shared slots. -/
theorem shared_listed_injective (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (good : ¬ context.collision sample) (kind : Pipeline.FixedKeyKind)
    (position : Fin coordinateBitCount) (slot : Fin 2) :
    Function.Injective (fun entry : SharedSlotRole slot.castSucc ×
        Fin (circuitBucketSize ⟨kind, position, .hash 0⟩) =>
      ((context.gates sample (circuitBucketGate ⟨kind, position, entry.1.1⟩ entry.2)).slotRecord entry.1.1).domain) ∧
    Function.Injective (fun entry : SharedSlotRole slot.castSucc ×
        Fin (circuitBucketSize ⟨kind, position, .hash 0⟩) =>
      ((context.gates sample (circuitBucketGate ⟨kind, position, entry.1.1⟩ entry.2)).slotRecord entry.1.1).range) := by
  cases kind with
  | curve adaptor =>
      cases adaptor
      · simpa only [circuitBucketGate, circuitBucketSize] using
          curve_role_assignments_injective context sample good 3 position slot
      · simpa only [circuitBucketGate, circuitBucketSize] using
          curve_role_assignments_injective context sample good 4 position slot
      · simpa only [circuitBucketGate, circuitBucketSize] using
          curve_role_assignments_injective context sample good 0 position slot
      · simpa only [circuitBucketGate, circuitBucketSize] using
          curve_role_assignments_injective context sample good 1 position slot
      · simpa only [circuitBucketGate, circuitBucketSize] using
          curve_role_assignments_injective context sample good 2 position slot
  | point coordinate adaptor =>
      cases coordinate <;> cases adaptor
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_role_assignments_injective context sample good (.inl 0) position slot
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_role_assignments_injective context sample good (.inl 1) position slot
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_role_assignments_injective context sample good (.inl 2) position slot
      · exact ⟨fun first => Fin.elim0 first.2, fun first => Fin.elim0 first.2⟩
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_role_assignments_injective context sample good (.inl 3) position slot
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_role_assignments_injective context sample good (.inr (.inl 0)) position slot
      · exact ⟨fun first => Fin.elim0 first.2, fun first => Fin.elim0 first.2⟩
      · exact ⟨fun first => Fin.elim0 first.2, fun first => Fin.elim0 first.2⟩
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_role_assignments_injective context sample good (.inr (.inl 1)) position slot
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_role_assignments_injective context sample good (.inr (.inl 2)) position slot
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_role_assignments_injective context sample good (.inr (.inr 0)) position slot
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_role_assignments_injective context sample good (.inr (.inr 1)) position slot
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_role_assignments_injective context sample good (.inr (.inr 2)) position slot
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_role_assignments_injective context sample good (.inr (.inr 3)) position slot
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_role_assignments_injective context sample good (.inr (.inr 4)) position slot


/-- The last point slot has distinct domains and ranges on every good retained row source. -/
theorem point_last_assignments_injective (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (good : ¬ context.collision sample) (family : PointGateFamily)
    (position : Fin coordinateBitCount) :
    Function.Injective (fun entry : SharedSlotRole 2 × Fin FieldMacToECMac.outputMacCount =>
      ((context.gates sample (pointRawGate entry.2 family position)).slotRecord entry.1.1).domain) ∧
    Function.Injective (fun entry : SharedSlotRole 2 × Fin FieldMacToECMac.outputMacCount =>
      ((context.gates sample (pointRawGate entry.2 family position)).slotRecord entry.1.1).range) := by
  have offsets := pointBranchCollision_false_injective context.visible.2 context.rows context.input
    context.targets sample.1.2 (fun event => good (Or.inl event)) family position (.hash 2)
  constructor
  · intro first second equal
    apply Prod.ext (Subsingleton.elim _ _)
    dsimp only at equal
    rw [point_raw_domain, point_raw_domain, sharedLastRole first.1, sharedLastRole second.1] at equal
    exact slotInput_injective _ pointSharedBranches_tweaks_injective _ equal
  · intro first second equal
    apply Prod.ext (Subsingleton.elim _ _)
    dsimp only at equal
    rw [point_raw_range, point_raw_range, sharedLastRole first.1, sharedLastRole second.1] at equal
    exact slotOutput_injective _ offsets _ equal

/-- Good retained data gives distinct listed assignments in the last public slot. -/
theorem last_listed_injective (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (good : ¬ context.collision sample) (kind : Pipeline.FixedKeyKind)
    (position : Fin coordinateBitCount) :
    Function.Injective (fun entry : SharedSlotRole 2 ×
        Fin (circuitBucketSize ⟨kind, position, .hash 0⟩) =>
      ((context.gates sample (circuitBucketGate ⟨kind, position, entry.1.1⟩ entry.2)).slotRecord entry.1.1).domain) ∧
    Function.Injective (fun entry : SharedSlotRole 2 ×
        Fin (circuitBucketSize ⟨kind, position, .hash 0⟩) =>
      ((context.gates sample (circuitBucketGate ⟨kind, position, entry.1.1⟩ entry.2)).slotRecord entry.1.1).range) := by
  cases kind with
  | curve adaptor =>
      have same (first second : SharedSlotRole 2 × Fin 1) : first = second := Subsingleton.elim _ _
      exact ⟨fun first second _ => same first second, fun first second _ => same first second⟩
  | point coordinate adaptor =>
      cases coordinate <;> cases adaptor
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_last_assignments_injective context sample good (.inl 0) position
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_last_assignments_injective context sample good (.inl 1) position
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_last_assignments_injective context sample good (.inl 2) position
      · exact ⟨fun first => Fin.elim0 first.2, fun first => Fin.elim0 first.2⟩
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_last_assignments_injective context sample good (.inl 3) position
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_last_assignments_injective context sample good (.inr (.inl 0)) position
      · exact ⟨fun first => Fin.elim0 first.2, fun first => Fin.elim0 first.2⟩
      · exact ⟨fun first => Fin.elim0 first.2, fun first => Fin.elim0 first.2⟩
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_last_assignments_injective context sample good (.inr (.inl 1)) position
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_last_assignments_injective context sample good (.inr (.inl 2)) position
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_last_assignments_injective context sample good (.inr (.inr 0)) position
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_last_assignments_injective context sample good (.inr (.inr 1)) position
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_last_assignments_injective context sample good (.inr (.inr 2)) position
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_last_assignments_injective context sample good (.inr (.inr 3)) position
      · simpa only [circuitBucketGate, circuitBucketSize, pointRawGate] using
          point_last_assignments_injective context sample good (.inr (.inr 4)) position


/-- The retained source supplies injective domains and ranges in every actual shared raw bucket. -/
theorem raw_assignments_injective (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (good : ¬ context.collision sample) (index : Shared.FixedKeyIndex) :
    Function.Injective (sharedRawBucketDomain (context.gates sample) index) ∧
    Function.Injective (sharedRawBucketRange (context.gates sample) index) := by
  have listed (current : Shared.FixedKeyIndex) :
      Function.Injective (fun entry : SharedSlotRole current.slot ×
          Fin (circuitBucketSize ⟨current.kind, current.position, .hash 0⟩) =>
        ((context.gates sample (circuitBucketGate ⟨current.kind, current.position, entry.1.1⟩ entry.2)).slotRecord
          entry.1.1).domain) ∧
      Function.Injective (fun entry : SharedSlotRole current.slot ×
          Fin (circuitBucketSize ⟨current.kind, current.position, .hash 0⟩) =>
        ((context.gates sample (circuitBucketGate ⟨current.kind, current.position, entry.1.1⟩ entry.2)).slotRecord
          entry.1.1).range) := by
    rcases current with ⟨kind, position, slot⟩
    fin_cases slot
    · exact shared_listed_injective context sample good kind position 0
    · exact shared_listed_injective context sample good kind position 1
    · exact last_listed_injective context sample good kind position
  have checked := listed index
  constructor
  · intro first second equal
    apply (context.bucketEquiv sample index).injective
    apply checked.1
    have firstValue := bucket_domain_listed context sample index (context.bucketEquiv sample index first)
    have secondValue := bucket_domain_listed context sample index (context.bucketEquiv sample index second)
    simp only [Equiv.symm_apply_apply] at firstValue secondValue
    exact firstValue.symm.trans (equal.trans secondValue)
  · intro first second equal
    apply (context.bucketEquiv sample index).injective
    apply checked.2
    have firstValue := bucket_range_listed context sample index (context.bucketEquiv sample index first)
    have secondValue := bucket_range_listed context sample index (context.bucketEquiv sample index second)
    simp only [Equiv.symm_apply_apply] at firstValue secondValue
    exact firstValue.symm.trans (equal.trans secondValue)

end SharedRetained
end
end Kriterion.ArgoMAC.Security
