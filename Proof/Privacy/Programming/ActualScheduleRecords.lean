import Proof.Privacy.Collision.CircuitSlotRatio
import Proof.Privacy.Distribution.CircuitHashDistribution
import Proof.Privacy.Programming.ActualGateConstraints
import Proof.Privacy.Distribution.GateProgrammingDistribution

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

/-- This record retains the actual selected block and label. -/
def GateDirective.slotRecord (directive : GateDirective) (slot : Pipeline.FixedKeySlot) :
    PermutationRecord Pipeline.FixedKeyIndex Block :=
  fixedProgramRecord directive.location directive.window slot directive.label
    (match slot with
      | .hash index => liftHashBlocks directive.lift.1 index
      | .pad index => targetPadBlocks directive.table directive.target index)

/-- This record writes one of the five actual raw constraints. -/
def RawGatePrescription.slotRecord (gate : RawGatePrescription) (slot : Pipeline.FixedKeySlot) :
    PermutationRecord Pipeline.FixedKeyIndex Block :=
  fixedProgramRecord gate.location gate.window slot (gate.label slot) (gate.offset slot)

/-- A selected directive gives the raw constraint for its selected branch. -/
theorem GateDirective.slotRecord_eq_raw (directive : GateDirective) (gate : RawGatePrescription)
    (slot : Pipeline.FixedKeySlot) (active : rawSlotBranch slot = directive.bit)
    (location : directive.location = gate.location) (window : directive.window = gate.window)
    (label : directive.label = if directive.bit then gate.key.trueLabel else gate.key.falseLabel)
    (table : directive.table = gate.table)
    (hashBlocks : directive.bit = false →
      liftHashBlocks directive.lift.1 = fullHashLiftBlockEquiv gate.lift)
    (padTarget : directive.bit = true → directive.target = gate.slope + (gate.lift.val : BaseField)) :
    directive.slotRecord slot = gate.slotRecord slot := by
  have congruent (selectedLabel selectedBlock rawLabel rawBlock : Block)
      (sameLabel : selectedLabel = rawLabel) (sameBlock : selectedBlock = rawBlock) :
      fixedProgramRecord directive.location directive.window slot selectedLabel selectedBlock =
        fixedProgramRecord gate.location gate.window slot rawLabel rawBlock := by
    rw [location, window, sameLabel, sameBlock]
  cases slot with
  | hash index =>
      have branch : directive.bit = false := active.symm
      have sameLabel : directive.label = gate.key.falseLabel := by
        simpa only [branch, Bool.false_eq_true, if_false] using label
      exact congruent _ _ _ _ sameLabel (congrFun (hashBlocks branch) index)
  | pad index =>
      have branch : directive.bit = true := active.symm
      have sameLabel : directive.label = gate.key.trueLabel := by
        simpa only [branch, if_true] using label
      apply congruent _ _ _ _ sameLabel
      exact congrArg₂ (fun table target => targetPadBlocks table target index) table (padTarget branch)

/-- This function keeps every field of an actual bit directive. -/
def actualDigitDirective {count : Nat} (location : Pipeline.FixedKeyLocation)
    (tables : Vector BitAdaptor.Table count) (values : Fin count → Bool)
    (labels : Vector Block count) (targets : Fin count → BaseField)
    (lifts : ∀ index, HashLift (targets index)) (index : Fin count) : GateDirective :=
  ⟨location, index.val, values index, labels.get index, tables.get index,
    targets index, lifts index⟩

private theorem mem_digitGateSchedule {count : Nat} (location : Pipeline.FixedKeyLocation)
    (tables : Vector BitAdaptor.Table count) (values : Fin count → Bool)
    (labels : Vector Block count) (targets : Fin count → BaseField)
    (lifts : ∀ index, HashLift (targets index)) (directive : GateDirective) :
    directive ∈ digitGateSchedule location tables values labels targets lifts ↔
      ∃ index, actualDigitDirective location tables values labels targets lifts index = directive := by
  exact List.mem_ofFn

def CurveGateRequest.actualDirective (request : CurveGateRequest)
    (input : AffineInput) (inputMac : InputMac)
    (adaptor : Fin 5) (bit : Fin coordinateBitCount) : GateDirective :=
  (![actualDigitDirective (.curve .x3) request.x3Table (coordinateValues input.x)
      inputMac.x request.x3Targets request.x3Lifts,
    actualDigitDirective (.curve .x5) request.x5Table (coordinateValues input.x)
      inputMac.x request.x5Targets request.x5Lifts,
    actualDigitDirective (.curve .x7) request.x7Table (coordinateValues input.x)
      inputMac.x request.x7Targets request.x7Lifts,
    actualDigitDirective (.curve .y4) request.y4Table (coordinateValues input.y)
      inputMac.y request.y4Targets request.y4Lifts,
    actualDigitDirective (.curve .y6) request.y6Table (coordinateValues input.y)
      inputMac.y request.y6Targets request.y6Lifts] adaptor) bit

def BiquadraticXRequest.actualDirective (request : BiquadraticXRequest)
    (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac)
    (adaptor : Fin 4) (bit : Fin coordinateBitCount) : GateDirective :=
  (![actualDigitDirective (.point output .x .y6) request.y6Table (coordinateValues input.y)
      inputMac.y request.y6Targets request.y6Lifts,
    actualDigitDirective (.point output .x .y8) request.y8Table (coordinateValues input.y)
      inputMac.y request.y8Targets request.y8Lifts,
    actualDigitDirective (.point output .x .y10) request.y10Table (coordinateValues input.y)
      inputMac.y request.y10Targets request.y10Lifts,
    actualDigitDirective (.point output .x .x9) request.x9Table (coordinateValues input.x)
      inputMac.x request.x9Targets request.x9Lifts] adaptor) bit

def BiquadraticYRequest.actualDirective (request : BiquadraticYRequest)
    (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac)
    (adaptor : Fin 3) (bit : Fin coordinateBitCount) : GateDirective :=
  (![actualDigitDirective (.point output .y .y6) request.y6Table (coordinateValues input.x)
      inputMac.x request.y6Targets request.y6Lifts,
    actualDigitDirective (.point output .y .x7) request.x7Table (coordinateValues input.x)
      inputMac.x request.x7Targets request.x7Lifts,
    actualDigitDirective (.point output .y .x9) request.x9Table (coordinateValues input.x)
      inputMac.x request.x9Targets request.x9Lifts] adaptor) bit

def BiquadraticZRequest.actualDirective (request : BiquadraticZRequest)
    (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac)
    (adaptor : Fin 5) (bit : Fin coordinateBitCount) : GateDirective :=
  (![actualDigitDirective (.point output .z .y6) request.y6Table (coordinateValues input.y)
      inputMac.y request.y6Targets request.y6Lifts,
    actualDigitDirective (.point output .z .y8) request.y8Table (coordinateValues input.y)
      inputMac.y request.y8Targets request.y8Lifts,
    actualDigitDirective (.point output .z .y10) request.y10Table (coordinateValues input.y)
      inputMac.y request.y10Targets request.y10Lifts,
    actualDigitDirective (.point output .z .x7) request.x7Table (coordinateValues input.x)
      inputMac.x request.x7Targets request.x7Lifts,
    actualDigitDirective (.point output .z .x9) request.x9Table (coordinateValues input.x)
      inputMac.x request.x9Targets request.x9Lifts] adaptor) bit

/-- This map indexes every directive of the actual circuit schedule. -/
def actualCircuitDirective (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveInputMac pointInputMac : InputMac) :
    RawCircuitGate → GateDirective
  | .inl (adaptor, bit) => curve.actualDirective input curveInputMac adaptor bit
  | .inr (row, .inl (adaptor, bit)) =>
      (points.get row).x.actualDirective row input pointInputMac adaptor bit
  | .inr (row, .inr (.inl (adaptor, bit))) =>
      (points.get row).y.actualDirective row input pointInputMac adaptor bit
  | .inr (row, .inr (.inr (adaptor, bit))) =>
      (points.get row).z.actualDirective row input pointInputMac adaptor bit

private theorem mem_four {α : Type} (a b c d : List α) (value : α) :
    value ∈ a ++ b ++ c ++ d ↔ ∃ index : Fin 4, value ∈ ![a,b,c,d] index := by
  simp [Fin.exists_fin_succ]

private theorem mem_three {α : Type} (a b c : List α) (value : α) :
    value ∈ a ++ b ++ c ↔ ∃ index : Fin 3, value ∈ ![a,b,c] index := by
  simp [Fin.exists_fin_succ]

private theorem mem_five {α : Type} (a b c d e : List α) (value : α) :
    value ∈ a ++ b ++ c ++ d ++ e ↔ ∃ index : Fin 5, value ∈ ![a,b,c,d,e] index := by
  simp [Fin.exists_fin_succ]

theorem CurveGateRequest.mem_schedule_iff (request : CurveGateRequest)
    (input : AffineInput) (inputMac : InputMac) (directive : GateDirective) :
    directive ∈ request.schedule input inputMac ↔
      ∃ adaptor bit, request.actualDirective input inputMac adaptor bit = directive := by
  unfold CurveGateRequest.schedule
  rw [mem_five]
  apply exists_congr
  intro adaptor
  fin_cases adaptor <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
      <;> rw [mem_digitGateSchedule]
      <;> rfl

theorem BiquadraticXRequest.mem_schedule_iff (request : BiquadraticXRequest)
    (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) (directive : GateDirective) :
    directive ∈ request.schedule output input inputMac ↔
      ∃ adaptor bit, request.actualDirective output input inputMac adaptor bit = directive := by
  unfold BiquadraticXRequest.schedule
  unfold biquadraticXGateSchedule
  rw [mem_four]
  apply exists_congr
  intro adaptor
  fin_cases adaptor <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
      <;> rw [mem_digitGateSchedule]
      <;> rfl

theorem BiquadraticYRequest.mem_schedule_iff (request : BiquadraticYRequest)
    (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) (directive : GateDirective) :
    directive ∈ request.schedule output input inputMac ↔
      ∃ adaptor bit, request.actualDirective output input inputMac adaptor bit = directive := by
  unfold BiquadraticYRequest.schedule
  unfold biquadraticYGateSchedule
  rw [mem_three]
  apply exists_congr
  intro adaptor
  fin_cases adaptor <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
      <;> rw [mem_digitGateSchedule]
      <;> rfl

theorem BiquadraticZRequest.mem_schedule_iff (request : BiquadraticZRequest)
    (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) (directive : GateDirective) :
    directive ∈ request.schedule output input inputMac ↔
      ∃ adaptor bit, request.actualDirective output input inputMac adaptor bit = directive := by
  unfold BiquadraticZRequest.schedule
  unfold biquadraticZGateSchedule
  rw [mem_five]
  apply exists_congr
  intro adaptor
  fin_cases adaptor <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
      <;> rw [mem_digitGateSchedule]
      <;> rfl

private theorem mem_flatten_ofFn {α : Type} {count : Nat}
    (lists : Fin count → List α) (value : α) :
    value ∈ (List.ofFn lists).flatten ↔ ∃ index, value ∈ lists index := by
  simp only [List.mem_flatten, List.mem_ofFn, exists_exists_eq_and]

theorem mem_pipelineGateSchedule_iff (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveInputMac pointInputMac : InputMac) (directive : GateDirective) :
    directive ∈ pipelineGateSchedule curve points input curveInputMac pointInputMac ↔
      ∃ gate, actualCircuitDirective curve points input curveInputMac pointInputMac gate = directive := by
  rw [pipelineGateSchedule, List.mem_append, CurveGateRequest.mem_schedule_iff]
  change _ ∨ directive ∈ (List.ofFn fun row =>
    (points.get row).schedule row input pointInputMac).flatten ↔ _
  rw [mem_flatten_ofFn]
  simp only [BiquadraticRowRequest.schedule, biquadraticRowGateSchedule, List.mem_append,
    BiquadraticXRequest.mem_schedule_iff, BiquadraticYRequest.mem_schedule_iff,
    BiquadraticZRequest.mem_schedule_iff, Sum.exists, Prod.exists, actualCircuitDirective,
    or_assoc]


theorem actualCircuitDirective_location (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveInputMac pointInputMac : InputMac) (gate : RawCircuitGate) :
    (actualCircuitDirective curve points input curveInputMac pointInputMac gate).location =
      rawCircuitLocation gate := by
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · fin_cases adaptor <;> rfl
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;>
      fin_cases adaptor <;> rfl

theorem actualCircuitDirective_window (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveInputMac pointInputMac : InputMac) (gate : RawCircuitGate) :
    (actualCircuitDirective curve points input curveInputMac pointInputMac gate).window =
      rawCircuitWindow gate := by
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · fin_cases adaptor <;> rfl
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;>
      fin_cases adaptor <;> rfl

private theorem exists_fixedKeySlot (predicate : Pipeline.FixedKeySlot → Prop) :
    (∃ slot, predicate slot) ↔
      (∃ index, predicate (.hash index)) ∨ (∃ index, predicate (.pad index)) := by
  constructor
  · rintro ⟨slot, proof⟩
    cases slot with
    | hash index => exact Or.inl ⟨index, proof⟩
    | pad index => exact Or.inr ⟨index, proof⟩
  · rintro (⟨index, proof⟩ | ⟨index, proof⟩)
    · exact ⟨.hash index, proof⟩
    · exact ⟨.pad index, proof⟩

theorem GateDirective.mem_programRecords_iff (directive : GateDirective)
    (record : PermutationRecord Pipeline.FixedKeyIndex Block) :
    record ∈ directive.programRecords ↔ ∃ slot,
      rawSlotBranch slot = directive.bit ∧ directive.slotRecord slot = record := by
  cases selected : directive.bit <;>
    simp only [GateDirective.programRecords, selected, Bool.false_eq_true, if_false, if_true,
      List.mem_cons, List.not_mem_nil, or_false, exists_fixedKeySlot,
      rawSlotBranch, Bool.true_eq_false, false_and, exists_false, false_or, true_and,
      GateDirective.slotRecord]
  all_goals simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false]
  · constructor
    · rintro (last | middle | first)
      · exact Or.inr (Or.inr last.symm)
      · exact Or.inr (Or.inl middle.symm)
      · exact Or.inl first.symm
    · rintro (first | middle | last)
      · exact Or.inr (Or.inr first.symm)
      · exact Or.inr (Or.inl middle.symm)
      · exact Or.inl last.symm
  · constructor
    · rintro (last | first)
      · exact Or.inr last.symm
      · exact Or.inl first.symm
    · rintro (first | last)
      · exact Or.inr first.symm
      · exact Or.inl last.symm

/-- The actual programming list contains exactly the selected raw gate slots. -/
theorem mem_pipelineGateProgramRecords_iff
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveInputMac pointInputMac : InputMac)
    (record : PermutationRecord Pipeline.FixedKeyIndex Block) :
    record ∈ gateProgramRecords
        (pipelineGateSchedule curve points input curveInputMac pointInputMac) ↔
      ∃ gate slot,
        rawSlotBranch slot =
          (actualCircuitDirective curve points input curveInputMac pointInputMac gate).bit ∧
        (actualCircuitDirective curve points input curveInputMac pointInputMac gate).slotRecord slot =
          record := by
  simp only [gateProgramRecords, List.mem_flatMap, List.mem_reverse,
    mem_pipelineGateSchedule_iff, GateDirective.mem_programRecords_iff]
  constructor
  · rintro ⟨directive, ⟨gate, rfl⟩, slot, active, same⟩
    exact ⟨gate, slot, active, same⟩
  · rintro ⟨gate, slot, active, same⟩
    exact ⟨_, ⟨gate, rfl⟩, slot, active, same⟩

/-- The selected record uses the actual shared permutation bucket. -/
theorem actualCircuitDirective_slotRecord_index
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveInputMac pointInputMac : InputMac)
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot) :
    ((actualCircuitDirective curve points input curveInputMac pointInputMac gate).slotRecord slot).index =
      fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot := by
  simp only [GateDirective.slotRecord, fixedProgramRecord, actualCircuitDirective_location,
    actualCircuitDirective_window]

/-- Every bucket selects one coordinate bit. -/
def circuitBucketInputBit (input : AffineInput) (bucket : RawLabelBucket) : Bool :=
  match bucket.1 with
  | .curve .x3 | .curve .x5 | .curve .x7 => coordinateValues input.x bucket.2
  | .curve .y4 | .curve .y6 => coordinateValues input.y bucket.2
  | .point _ .x7 | .point _ .x9 | .point .y .y6 => coordinateValues input.x bucket.2
  | .point .x .y6 | .point .z .y6
  | .point _ .y8 | .point _ .y10 => coordinateValues input.y bucket.2

/-- Every bucket uses one selected coordinate label. -/
def circuitBucketInputLabel (curveInputMac pointInputMac : InputMac)
    (bucket : RawLabelBucket) : Block :=
  match bucket.1 with
  | .curve .x3 | .curve .x5 | .curve .x7 => curveInputMac.x.get bucket.2
  | .curve .y4 | .curve .y6 => curveInputMac.y.get bucket.2
  | .point _ .x7 | .point _ .x9 | .point .y .y6 => pointInputMac.x.get bucket.2
  | .point .x .y6 | .point .z .y6
  | .point _ .y8 | .point _ .y10 => pointInputMac.y.get bucket.2

theorem actualCircuitDirective_bit
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveInputMac pointInputMac : InputMac)
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot) :
    (actualCircuitDirective curve points input curveInputMac pointInputMac gate).bit =
      circuitBucketInputBit input (rawLabelBucket
        (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) := by
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · fin_cases adaptor <;>
      simp [actualCircuitDirective, CurveGateRequest.actualDirective, actualDigitDirective,
        circuitBucketInputBit, rawLabelBucket, fixedKeyIndex, rawCircuitLocation,
        rawCircuitWindow, Pipeline.FixedKeyLocation.kind, Nat.mod_eq_of_lt bit.isLt]
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;>
      fin_cases adaptor <;>
      simp [actualCircuitDirective, BiquadraticXRequest.actualDirective,
        BiquadraticYRequest.actualDirective, BiquadraticZRequest.actualDirective,
        actualDigitDirective, circuitBucketInputBit, rawLabelBucket, fixedKeyIndex,
        rawCircuitLocation, rawCircuitWindow, Pipeline.FixedKeyLocation.kind,
        Nat.mod_eq_of_lt bit.isLt]

theorem actualCircuitDirective_label
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveInputMac pointInputMac : InputMac)
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot) :
    (actualCircuitDirective curve points input curveInputMac pointInputMac gate).label =
      circuitBucketInputLabel curveInputMac pointInputMac (rawLabelBucket
        (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) := by
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · fin_cases adaptor <;>
      simp [actualCircuitDirective, CurveGateRequest.actualDirective, actualDigitDirective,
        circuitBucketInputLabel, rawLabelBucket, fixedKeyIndex, rawCircuitLocation,
        rawCircuitWindow, Pipeline.FixedKeyLocation.kind, Nat.mod_eq_of_lt bit.isLt]
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;>
      fin_cases adaptor <;>
      simp [actualCircuitDirective, BiquadraticXRequest.actualDirective,
        BiquadraticYRequest.actualDirective, BiquadraticZRequest.actualDirective,
        actualDigitDirective, circuitBucketInputLabel, rawLabelBucket, fixedKeyIndex,
        rawCircuitLocation, rawCircuitWindow, Pipeline.FixedKeyLocation.kind,
        Nat.mod_eq_of_lt bit.isLt]

/-- The raw gate constraints characterize the actual selected transcript. -/
theorem pipelineGateProgramRecords_matches_iff
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveInputMac pointInputMac : InputMac)
    (gates : RawCircuitGate → RawGatePrescription)
    (recordLaw : ∀ gate slot,
      rawSlotBranch slot =
        (actualCircuitDirective curve points input curveInputMac pointInputMac gate).bit →
      (actualCircuitDirective curve points input curveInputMac pointInputMac gate).slotRecord slot =
        (gates gate).slotRecord slot)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) :
    PermutationTranscriptMatches oracle (gateProgramRecords
        (pipelineGateSchedule curve points input curveInputMac pointInputMac)) ↔
      ∀ gate slot,
        rawSlotBranch slot =
          (actualCircuitDirective curve points input curveInputMac pointInputMac gate).bit →
        oracle.permutation (fixedKeyIndex (gates gate).location (gates gate).window slot)
          (gateInput (gates gate).location ((gates gate).label slot)) =
          (gates gate).offset slot ^^^ (gates gate).label slot := by
  constructor
  · intro compatible gate slot active
    have member := (mem_pipelineGateProgramRecords_iff curve points input curveInputMac
      pointInputMac _).mpr ⟨gate, slot, active, rfl⟩
    have matched := compatible _ member
    rw [recordLaw gate slot active] at matched
    exact matched
  · intro compatible record member
    rcases (mem_pipelineGateProgramRecords_iff curve points input curveInputMac pointInputMac
      record).mp member with ⟨gate, slot, active, rfl⟩
    rw [recordLaw gate slot active]
    exact compatible gate slot active

/-- This theorem gives the active equations used by the shared-bucket count. -/
theorem pipelineGateProgramRecords_referenceActive
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveInputMac pointInputMac : InputMac)
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (recordLaw : ∀ gate slot,
      rawSlotBranch slot =
        (actualCircuitDirective curve points input curveInputMac pointInputMac gate).bit →
      (actualCircuitDirective curve points input curveInputMac pointInputMac gate).slotRecord slot =
        (circuitRawGatePrescription keys slopes lifts tables gate).slotRecord slot)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (compatible : PermutationTranscriptMatches oracle (gateProgramRecords
      (pipelineGateSchedule curve points input curveInputMac pointInputMac))) :
    ∀ index, rawSlotBranch index.slot = circuitBucketInputBit input (rawLabelBucket index) →
      ∀ use : RawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index,
        oracle.permutation index
          (circuitBucketInputLabel curveInputMac pointInputMac (rawLabelBucket index) ^^^
            rawBucketTweak (circuitRawGatePrescription keys slopes lifts tables) index use) =
          rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index use ^^^
            circuitBucketInputLabel curveInputMac pointInputMac (rawLabelBucket index) := by
  intro index active use
  rcases use with ⟨⟨gate, slot⟩, sameIndex⟩
  subst index
  have selected : rawSlotBranch slot =
      (actualCircuitDirective curve points input curveInputMac pointInputMac gate).bit := by
    rw [actualCircuitDirective_bit curve points input curveInputMac pointInputMac gate slot]
    exact active
  have rawLaw := recordLaw gate slot selected
  have labelLaw : (circuitRawGatePrescription keys slopes lifts tables gate).label slot =
      circuitBucketInputLabel curveInputMac pointInputMac
        (rawLabelBucket (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) := by
    have domains := congrArg PermutationRecord.domain rawLaw
    change (actualCircuitDirective curve points input curveInputMac pointInputMac gate).label ^^^
      (actualCircuitDirective curve points input curveInputMac pointInputMac gate).location.tweak =
      (circuitRawGatePrescription keys slopes lifts tables gate).label slot ^^^
        (rawCircuitLocation gate).tweak at domains
    rw [actualCircuitDirective_location, actualCircuitDirective_label curve points input
      curveInputMac pointInputMac gate slot] at domains
    have cancelled := congrArg (fun value => value ^^^ (rawCircuitLocation gate).tweak) domains
    simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using cancelled.symm
  have matched := (pipelineGateProgramRecords_matches_iff curve points input curveInputMac
    pointInputMac _ recordLaw oracle).mp compatible gate slot selected
  rw [labelLaw] at matched
  exact matched

/-- The source gives the table of every actual selected directive. -/
theorem circuitMaskDirective_table (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows)
    (input : AffineInput) (source : CircuitMaskSample) (curveInputMac pointInputMac : InputMac)
    (gate : RawCircuitGate) :
    let sample := circuitMaskSampleGarble bridgeKey mask rows input source
    (actualCircuitDirective sample.curveRequest sample.pointRequests input curveInputMac
      pointInputMac gate).table = circuitSourceTable source gate := by
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · fin_cases adaptor <;> rfl
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;>
      fin_cases adaptor <;>
      simp only [actualCircuitDirective, circuitMaskSampleGarble, PublicSample.pointRequests,
        Vector.get_map, Vector.get_ofFn] <;> rfl

/-- The source gives the actual false or true field target at every gate. -/
theorem circuitMaskDirective_target (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows)
    (input : AffineInput) (source : CircuitMaskSample) (curveInputMac pointInputMac : InputMac)
    (gate : RawCircuitGate) :
    let sample := circuitMaskSampleGarble bridgeKey mask rows input source
    let directive := actualCircuitDirective sample.curveRequest sample.pointRequests input
      curveInputMac pointInputMac gate
    directive.target = if directive.bit then
      circuitSourceSlope source gate + circuitSourceField source gate else circuitSourceField source gate := by
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · fin_cases adaptor <;> rfl
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;>
      fin_cases adaptor <;>
      simp only [actualCircuitDirective, circuitMaskSampleGarble, PublicSample.pointRequests,
        Vector.get_map, Vector.get_ofFn] <;> rfl

theorem circuitMaskHashSplit_field (source : CircuitMaskSample) (gate : RawCircuitGate) :
    ((circuitMaskHashSplitEquiv source).1 gate).1 = circuitSourceField source gate := by
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · rfl
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;> rfl

theorem goodHashLiftSource_field (sample : BaseField × HashLiftQuotient) :
    ((goodHashLiftSource sample).val : BaseField) = sample.1 := by
  rw [goodHashLiftSource_eq]
  exact (goodHashLift sample.1 sample.2).2

theorem goodHashLiftSource_blocks (sample : BaseField × HashLiftQuotient) :
    fullHashLiftBlockEquiv (goodHashLiftSource sample) =
      liftHashBlocks (goodHashLift sample.1 sample.2).1 := by
  rw [goodHashLiftSource_eq]
  rfl

/-- The actual record domains equal the selected domains in the raw count. -/
theorem pipelineGateProgramRecords_domains
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveInputMac pointInputMac : InputMac)
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (index : Pipeline.FixedKeyIndex) :
    {domain | ∃ record ∈ gateProgramRecords
        (pipelineGateSchedule curve points input curveInputMac pointInputMac),
      record.index = index ∧ record.domain = domain} =
      rawActiveDomains (circuitRawGatePrescription keys slopes lifts tables)
        (circuitBucketInputBit input) (circuitBucketInputLabel curveInputMac pointInputMac) index := by
  ext domain
  constructor
  · rintro ⟨record, member, sameIndex, sameDomain⟩
    rcases (mem_pipelineGateProgramRecords_iff curve points input curveInputMac pointInputMac
      record).mp member with ⟨gate, slot, active, rfl⟩
    have bucket : fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot = index :=
      (actualCircuitDirective_slotRecord_index curve points input curveInputMac pointInputMac
        gate slot).symm.trans sameIndex
    clear sameIndex
    subst index
    have selected : rawSlotBranch slot = circuitBucketInputBit input
        (rawLabelBucket (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) :=
      active.trans (actualCircuitDirective_bit curve points input curveInputMac pointInputMac gate slot)
    change rawSlotBranch (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot).slot =
      circuitBucketInputBit input
        (rawLabelBucket (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) at selected
    rw [rawActiveDomains, if_pos selected]
    refine ⟨⟨(gate, slot), rfl⟩, ?_⟩
    change (actualCircuitDirective curve points input curveInputMac pointInputMac gate).label ^^^
      (actualCircuitDirective curve points input curveInputMac pointInputMac gate).location.tweak = domain
      at sameDomain
    rw [actualCircuitDirective_label curve points input curveInputMac pointInputMac gate slot,
      actualCircuitDirective_location] at sameDomain
    exact sameDomain
  · intro member
    by_cases selected : rawSlotBranch index.slot = circuitBucketInputBit input (rawLabelBucket index)
    · rw [rawActiveDomains, if_pos selected] at member
      rcases member with ⟨⟨⟨gate, slot⟩, bucket⟩, sameDomain⟩
      subst index
      have active : rawSlotBranch slot =
          (actualCircuitDirective curve points input curveInputMac pointInputMac gate).bit := by
        rw [actualCircuitDirective_bit curve points input curveInputMac pointInputMac gate slot]
        exact selected
      refine ⟨_, (mem_pipelineGateProgramRecords_iff curve points input curveInputMac
        pointInputMac _).mpr ⟨gate, slot, active, rfl⟩,
        actualCircuitDirective_slotRecord_index curve points input curveInputMac pointInputMac gate slot, ?_⟩
      change (actualCircuitDirective curve points input curveInputMac pointInputMac gate).label ^^^
        (actualCircuitDirective curve points input curveInputMac pointInputMac gate).location.tweak = domain
      rw [actualCircuitDirective_label curve points input curveInputMac pointInputMac gate slot,
        actualCircuitDirective_location]
      exact sameDomain
    · simp only [rawActiveDomains, if_neg selected, Set.mem_empty_iff_false] at member

attribute [local instance] rawBucketUseFintype fixedQueryDomainFintype

/-- Every selected bucket has the exact number of distinct programmed domains. -/
theorem pipelineGateProgramRecords_domainCount [Fintype Block]
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveInputMac pointInputMac : InputMac)
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (index : Pipeline.FixedKeyIndex) :
    Fintype.card (FixedQueryDomain (gateProgramRecords
      (pipelineGateSchedule curve points input curveInputMac pointInputMac)) index) =
      if rawSlotBranch index.slot = circuitBucketInputBit input (rawLabelBucket index) then
        circuitBucketSize index else 0 := by
  classical
  let gates := circuitRawGatePrescription keys slopes lifts tables
  let domains := fun use : RawBucketUse gates index =>
    circuitBucketInputLabel curveInputMac pointInputMac (rawLabelBucket index) ^^^
      rawBucketTweak gates index use
  have domainLaw := pipelineGateProgramRecords_domains curve points input curveInputMac
    pointInputMac keys slopes lifts tables index
  by_cases active : rawSlotBranch index.slot = circuitBucketInputBit input (rawLabelBucket index)
  · rw [if_pos active]
    rw [rawActiveDomains, if_pos active] at domainLaw
    have injective : Function.Injective domains := by
      intro first second equal
      apply circuitRawBucketTweak_injective keys slopes lifts tables index
      have cancelled := congrArg (fun value =>
        circuitBucketInputLabel curveInputMac pointInputMac (rawLabelBucket index) ^^^ value) equal
      simpa only [domains, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using cancelled
    have equivalence : FixedQueryDomain (gateProgramRecords
        (pipelineGateSchedule curve points input curveInputMac pointInputMac)) index ≃
        RawBucketUse gates index :=
      (Equiv.setCongr domainLaw).trans (Equiv.ofInjective domains injective).symm
    exact (Fintype.card_congr equivalence).trans (circuitRawBucketUse_card keys slopes lifts tables index)
  · rw [if_neg active]
    rw [rawActiveDomains, if_neg active] at domainLaw
    letI : IsEmpty (FixedQueryDomain (gateProgramRecords
        (pipelineGateSchedule curve points input curveInputMac pointInputMac)) index) := ⟨fun value => by
      have member := value.property
      change value.val ∈ {domain | ∃ record ∈ gateProgramRecords
        (pipelineGateSchedule curve points input curveInputMac pointInputMac),
        record.index = index ∧ record.domain = domain} at member
      rw [domainLaw] at member
      exact member⟩
    exact Fintype.card_eq_zero

/-- This map retains the actual quotient at every public gate. -/
def publicCircuitQuotient (sample : PublicSample) : RawCircuitGate → HashLiftQuotient
  | .inl (adaptor, bit) => sample.curve.quotients adaptor bit
  | .inr (row, .inl (adaptor, bit)) => (sample.points.get row).x.quotients adaptor bit
  | .inr (row, .inr (.inl (adaptor, bit))) => (sample.points.get row).y.quotients adaptor bit
  | .inr (row, .inr (.inr (adaptor, bit))) => (sample.points.get row).z.quotients adaptor bit

/-- Every public directive uses its selected field target and retained quotient. -/
theorem publicCircuitDirective_lift (sample : PublicSample) (input : AffineInput)
    (curveInputMac pointInputMac : InputMac) (gate : RawCircuitGate) :
    let directive := actualCircuitDirective sample.curveRequest sample.pointRequests input
      curveInputMac pointInputMac gate
    directive.lift.1 = (goodHashLift directive.target (publicCircuitQuotient sample gate)).1 := by
  have points (row : Fin FieldMacToECMac.outputMacCount) :
      sample.pointRequests.get row = (sample.points.get row).request :=
    Vector.get_map sample.points RowPublicSample.request row
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · fin_cases adaptor <;> rfl
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;>
      fin_cases adaptor <;>
      simp only [actualCircuitDirective] <;> rw [points row] <;> rfl

/-- The mask source keeps the actual public quotient at every gate. -/
theorem circuitMaskDirective_quotient (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows)
    (input : AffineInput) (source : CircuitMaskSample) (gate : RawCircuitGate) :
    publicCircuitQuotient (circuitMaskSampleGarble bridgeKey mask rows input source) gate =
      ((circuitMaskHashSplitEquiv source).1 gate).2 := by
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · rfl
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;>
      simp only [publicCircuitQuotient, circuitMaskSampleGarble, Vector.get_ofFn] <;> rfl

/-- The complete source lift retains the exact selected target and quotient. -/
theorem circuitMaskDirective_lift (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows)
    (input : AffineInput) (source : CircuitMaskSample) (curveInputMac pointInputMac : InputMac)
    (gate : RawCircuitGate) :
    let sample := circuitMaskSampleGarble bridgeKey mask rows input source
    let directive := actualCircuitDirective sample.curveRequest sample.pointRequests input
      curveInputMac pointInputMac gate
    directive.lift.1 = (goodHashLift directive.target ((circuitMaskHashSplitEquiv source).1 gate).2).1 := by
  have law := publicCircuitDirective_lift (circuitMaskSampleGarble bridgeKey mask rows input source)
    input curveInputMac pointInputMac gate
  dsimp only at law ⊢
  rw [circuitMaskDirective_quotient] at law
  exact law

/-- Every selected directive uses the actual encoded label of its source key. -/
theorem actualCircuitDirective_encodedLabel
    (curve : CurveGateRequest) (points : PointGateRequests) (input : AffineInput)
    (curveKey pointKey : InputMacKey) (gate : RawCircuitGate) :
    let directive := actualCircuitDirective curve points input (curveKey.encodeAffine input)
      (pointKey.encodeAffine input) gate
    directive.label = BitAdaptor.encode (circuitGateKey pointKey curveKey gate) directive.bit := by
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · fin_cases adaptor <;>
      simp [actualCircuitDirective, CurveGateRequest.actualDirective, actualDigitDirective,
        circuitGateKey, InputMacKey.encodeAffine, InputMacKey.encode, BitInput.ofAffine,
        encodeCoordinate, coordinateValues] <;> rfl
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;>
      fin_cases adaptor <;>
      simp [actualCircuitDirective, BiquadraticXRequest.actualDirective,
        BiquadraticYRequest.actualDirective, BiquadraticZRequest.actualDirective,
        actualDigitDirective, circuitGateKey, InputMacKey.encodeAffine, InputMacKey.encode,
        BitInput.ofAffine, encodeCoordinate, coordinateValues] <;> rfl

/-- The actual source proves every selected raw record equality. -/
theorem circuitMaskDirective_record_eq_raw (bridgeKey mask : BaseField)
    (rows : FieldMacToECMac.Rows) (input : AffineInput) (source : CircuitMaskSample)
    (curveKey pointKey : InputMacKey) (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot) :
    let sample := circuitMaskSampleGarble bridgeKey mask rows input source
    let directive := actualCircuitDirective sample.curveRequest sample.pointRequests input
      (curveKey.encodeAffine input) (pointKey.encodeAffine input) gate
    rawSlotBranch slot = directive.bit → directive.slotRecord slot =
      (sourceGatePrescription source pointKey curveKey
        (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)) gate).slotRecord slot := by
  dsimp only
  intro active
  apply GateDirective.slotRecord_eq_raw _ _ slot active
  · exact actualCircuitDirective_location _ _ _ _ _ gate
  · exact actualCircuitDirective_window _ _ _ _ _ gate
  · exact actualCircuitDirective_encodedLabel _ _ input curveKey pointKey gate
  · exact circuitMaskDirective_table bridgeKey mask rows input source _ _ gate
  · intro branch
    have target := circuitMaskDirective_target bridgeKey mask rows input source
      (curveKey.encodeAffine input) (pointKey.encodeAffine input) gate
    dsimp only at target
    simp only [branch, Bool.false_eq_true, if_false] at target
    have lifted := circuitMaskDirective_lift bridgeKey mask rows input source
      (curveKey.encodeAffine input) (pointKey.encodeAffine input) gate
    dsimp only at lifted
    have selectedLift := lifted.trans (congrArg (fun value : BaseField =>
      (goodHashLift value ((circuitMaskHashSplitEquiv source).1 gate).2).1) target)
    change liftHashBlocks _ = fullHashLiftBlockEquiv
      (goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
    rw [goodHashLiftSource_blocks, circuitMaskHashSplit_field]
    exact congrArg liftHashBlocks selectedLift
  · intro branch
    have target := circuitMaskDirective_target bridgeKey mask rows input source
      (curveKey.encodeAffine input) (pointKey.encodeAffine input) gate
    dsimp only at target
    simp only [branch, if_true] at target
    change _ = circuitSourceSlope source gate +
      ((goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)).val : BaseField)
    rw [goodHashLiftSource_field, circuitMaskHashSplit_field]
    exact target

end Kriterion.ArgoMAC.Security
