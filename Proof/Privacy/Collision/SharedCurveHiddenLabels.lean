import Proof.Privacy.Programming.SharedCurveRecords
import Proof.Privacy.Collision.SharedPrequeryBound

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 2048
attribute [local irreducible] Context.source Context.lifts

/-- The invalid branch samples the selected point labels as hidden labels. -/
def Context.curveHidden (context : Context) (key : InputMacKey) : Context :=
  {context with activePointLabels := fun index => inputKeyLabel key index true}

/-- The second hidden array supplies unused curve labels and shifted unused point labels. -/
def curveUnused (key : InputMacKey) : EncPRF.PermutationIndex → Block :=
  fun index => inputKeyLabel key index false

/-- A point record selects the first hidden array only on its selected input branch. -/
def curveHiddenBit (context : Context) (gate : RawCircuitGate) (branch : Bool) : Bool :=
  match gate with
  | .inl _ => false
  | .inr _ => branch == inputSelectedLabelBit context.input (circuitGateWire gate)

/-- The unused point label retains its independent linking pad. -/
def curveHiddenPad (context : Context) (gate : RawCircuitGate) (branch : Bool) : Block :=
  match gate with
  | .inl _ => 0
  | .inr _ => if branch = inputSelectedLabelBit context.input (circuitGateWire gate)
      then 0 else context.hiddenPointPads (circuitGateWire gate)

/-- Every hidden record reads one uniform label array with one fixed shift. -/
theorem curveHidden_label (context : Context) (key : InputMacKey)
    (gate : RawCircuitGate) (branch : Bool)
    (hidden : ¬ (sharedCurveSlot (Shared.fixedIndex
      (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) (.hash 0))) = true ∧
        branch = inputSelectedLabelBit context.input (circuitGateWire gate))) :
    (context.curveHidden key).gateLabel (curveUnused key) gate branch =
      inputKeyLabel key (circuitGateWire gate) (curveHiddenBit context gate branch) ^^^
        curveHiddenPad context gate branch := by
  cases gate with
  | inl gate =>
      have inactive : branch ≠ inputSelectedLabelBit context.input (circuitGateWire (.inl gate)) := by
        intro selected
        exact hidden ⟨rfl, selected⟩
      dsimp only [Context.gateLabel, Context.curveHidden, curveUnused, curveHiddenBit, curveHiddenPad]
      rw [if_neg inactive]
      exact BitVec.xor_zero.symm
  | inr gate =>
      by_cases selected : branch = inputSelectedLabelBit context.input (circuitGateWire (.inr gate))
      · dsimp only [Context.gateLabel, Context.curveHidden, curveUnused, curveHiddenBit, curveHiddenPad]
        rw [if_pos selected, if_pos selected, selected, beq_self_eq_true]
        exact BitVec.xor_zero.symm
      · dsimp only [Context.gateLabel, Context.curveHidden, curveUnused, curveHiddenBit, curveHiddenPad]
        rw [if_neg selected, if_neg selected, beq_eq_false_iff_ne.mpr selected]

/-- Each hidden query use keeps the source domain and range shifts. -/
def curveHiddenGateUse (context : Context) (hidden : HiddenPublicSample)
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot) : PrequeryLabelUse :=
  let shift := curveHiddenPad context gate (rawSlotBranch slot) ^^^ (rawCircuitLocation gate).tweak
  ⟨circuitGateWire gate, curveHiddenBit context gate (rawSlotBranch slot), shift,
    shift ^^^ circuitSourceOffset (context.source hidden) (context.lifts hidden) gate slot⟩

/-- The hidden use gives the exact shared source domain. -/
theorem curveHiddenGateUse_domain (context : Context) (hidden : HiddenPublicSample)
    (key : InputMacKey) (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot)
    (inactive : ¬ (sharedCurveSlot (Shared.fixedIndex
      (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) (.hash 0))) = true ∧
        rawSlotBranch slot = inputSelectedLabelBit context.input (circuitGateWire gate))) :
    let use := curveHiddenGateUse context hidden gate slot
    inputKeyLabel key use.index use.bit ^^^ use.domainShift =
      (((context.curveHidden key).gates (hidden, curveUnused key) gate).slotRecord slot).domain := by
  change _ = ((context.curveHidden key).gates (hidden, curveUnused key) gate).label slot ^^^
    (rawCircuitLocation gate).tweak
  rw [raw_gate_label, curveHidden_label context key gate (rawSlotBranch slot) inactive]
  exact (BitVec.xor_assoc _ _ _).symm

/-- The hidden use gives the exact shared source range. -/
theorem curveHiddenGateUse_range (context : Context) (hidden : HiddenPublicSample)
    (key : InputMacKey) (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot)
    (inactive : ¬ (sharedCurveSlot (Shared.fixedIndex
      (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) (.hash 0))) = true ∧
        rawSlotBranch slot = inputSelectedLabelBit context.input (circuitGateWire gate))) :
    let use := curveHiddenGateUse context hidden gate slot
    inputKeyLabel key use.index use.bit ^^^ use.rangeShift =
      (((context.curveHidden key).gates (hidden, curveUnused key) gate).slotRecord slot).range := by
  change _ = ((context.curveHidden key).gates (hidden, curveUnused key) gate).offset slot ^^^
    (((context.curveHidden key).gates (hidden, curveUnused key) gate).label slot ^^^ (rawCircuitLocation gate).tweak)
  have sourceEq : (context.curveHidden key).source hidden = context.source hidden := by
    unfold Context.source Context.curveHidden
    rfl
  have liftsEq : (context.curveHidden key).lifts hidden = context.lifts hidden := by
    unfold Context.lifts
    rw [sourceEq]
  rw [raw_gate_offset, sourceEq, liftsEq, raw_gate_label, curveHidden_label context key gate (rawSlotBranch slot) inactive]
  change inputKeyLabel key _ _ ^^^ (_ ^^^ circuitSourceOffset (context.source hidden) (context.lifts hidden) gate slot) =
    circuitSourceOffset (context.source hidden) (context.lifts hidden) gate slot ^^^ _
  ac_rfl

/-- The curve-only query enumeration includes every hidden point role. -/
def curveHiddenQueryUses (context : Context) (hidden : HiddenPublicSample)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (query : Fin history.length) (row : Fin (sharedCircuitBucketSize (history.get query).index)) :
    PrequeryLabelUse :=
  let use := sharedSourceBucketEquiv (context.source hidden) (context.lifts hidden) (history.get query).index row
  curveHiddenGateUse context hidden use.1.1 use.1.2

/-- The good query flag separates every hidden point and unused curve assignment. -/
theorem curveHiddenQuery_false_fresh (context : Context) (hidden : HiddenPublicSample)
    (key : InputMacKey) (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (good : ¬ sharedPrequeryLabelCollision history (curveHiddenQueryUses context hidden history) key)
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot)
    (inactive : ¬ (sharedCurveSlot (Shared.fixedIndex
      (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) (.hash 0))) = true ∧
        rawSlotBranch slot = inputSelectedLabelBit context.input (circuitGateWire gate))) :
    let record := ((context.curveHidden key).gates (hidden, curveUnused key) gate).slotRecord slot
    FreshPermutationPair history (Shared.fixedIndex record.index) record.domain record.range := by
  dsimp only
  intro prior member sameIndex
  obtain ⟨query, queryEqual⟩ := List.mem_iff_get.mp member
  let use : SharedRawBucketUse
      (circuitRawGatePrescription (fun _ => ⟨0, 0⟩) (circuitSourceSlope (context.source hidden))
        (context.lifts hidden) (circuitSourceTable (context.source hidden))) (history.get query).index :=
    ⟨(gate, slot), by rw [queryEqual]; exact sameIndex.symm⟩
  let row := (sharedSourceBucketEquiv (context.source hidden) (context.lifts hidden)
    (history.get query).index).symm use
  have selectedUse : curveHiddenQueryUses context hidden history query row =
      curveHiddenGateUse context hidden gate slot := by
    unfold curveHiddenQueryUses row
    rw [Equiv.apply_symm_apply]
  constructor
  · intro equal
    apply good
    refine ⟨query, row, Or.inl ?_⟩
    rw [selectedUse, curveHiddenGateUse_domain context hidden key gate slot inactive, queryEqual]
    exact equal.symm
  · intro equal
    apply good
    refine ⟨query, row, Or.inr ?_⟩
    rw [selectedUse, curveHiddenGateUse_range context hidden key gate slot inactive, queryEqual]
    exact equal.symm

/-- The query event pays at most 364 inverse blocks per public query. -/
theorem curveHiddenQuery_mass_le [Fintype Block]
    (context : Context) (hidden : HiddenPublicSample)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block)) :
    letI : Fintype InputMacKey := publicInputMacKeyFintype
    letI : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
      {key | sharedPrequeryLabelCollision history (curveHiddenQueryUses context hidden history) key} ≤
        (364 * history.length : Nat) / (Fintype.card Block : ENNReal) := by
  exact sharedPrequeryLabelCollision_mass_le history (curveHiddenQueryUses context hidden history)

end
end Kriterion.ArgoMAC.Security.SharedRetained
