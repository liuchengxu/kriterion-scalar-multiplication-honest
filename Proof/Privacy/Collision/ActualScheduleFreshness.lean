import Proof.Privacy.Programming.ActualScheduleRecords

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

private theorem nodup_of_enumerates {Index Value : Type*} [Fintype Index]
    (values : List Value) (enumerate : Index → Value)
    (injective : Function.Injective enumerate)
    (members : ∀ value, value ∈ values ↔ ∃ index, enumerate index = value)
    (length : values.length = Fintype.card Index) : values.Nodup := by
  classical
  have equal : values.toFinset = Finset.univ.image enumerate := by
    ext value
    simp only [List.mem_toFinset, members, Finset.mem_image, Finset.mem_univ, true_and]
  have count : values.toFinset.card = values.length := by
    rw [equal, Finset.card_image_of_injective _ injective, Finset.card_univ, length]
  exact (Multiset.toFinset_card_eq_card_iff_nodup (m := (values : Multiset Value))).mp count

set_option exponentiation.threshold 400 in
/-- Each actual gate slot has one distinct index and domain pair. -/
theorem actualCircuitSlotDomain_injective
    (curve : CurveGateRequest) (points : PointGateRequests) (input : AffineInput)
    (curveInputMac pointInputMac : InputMac) :
    Function.Injective (fun use : RawCircuitGate × Pipeline.FixedKeySlot =>
      let record := (actualCircuitDirective curve points input curveInputMac pointInputMac use.1).slotRecord use.2
      (record.index, record.domain)) := by
  intro first second same
  have indices : fixedKeyIndex (rawCircuitLocation first.1) (rawCircuitWindow first.1) first.2 =
      fixedKeyIndex (rawCircuitLocation second.1) (rawCircuitWindow second.1) second.2 :=
    (actualCircuitDirective_slotRecord_index curve points input curveInputMac pointInputMac
      first.1 first.2).symm.trans ((congrArg Prod.fst same).trans
      (actualCircuitDirective_slotRecord_index curve points input curveInputMac pointInputMac
        second.1 second.2))
  have domains := congrArg Prod.snd same
  change (actualCircuitDirective curve points input curveInputMac pointInputMac first.1).label ^^^
    (actualCircuitDirective curve points input curveInputMac pointInputMac first.1).location.tweak =
    (actualCircuitDirective curve points input curveInputMac pointInputMac second.1).label ^^^
      (actualCircuitDirective curve points input curveInputMac pointInputMac second.1).location.tweak at domains
  rw [actualCircuitDirective_label curve points input curveInputMac pointInputMac first.1 first.2,
    actualCircuitDirective_label curve points input curveInputMac pointInputMac second.1 second.2,
    actualCircuitDirective_location, actualCircuitDirective_location, indices] at domains
  have tweaks : (rawCircuitLocation first.1).tweak = (rawCircuitLocation second.1).tweak := by
    have cancelled := congrArg (fun value => circuitBucketInputLabel curveInputMac pointInputMac
      (rawLabelBucket (fixedKeyIndex (rawCircuitLocation second.1) (rawCircuitWindow second.1) second.2)) ^^^ value) domains
    simpa only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using cancelled
  let keys : RawCircuitGate → BitAdaptor.Key := fun _ => ⟨0, 0⟩
  let slopes : RawCircuitGate → BaseField := fun _ => 0
  let lifts : RawCircuitGate → FullHashLift := fun _ =>
    (actualCircuitDirective curve points input curveInputMac pointInputMac first.1).lift.1.toFin
  let tables := fun _ : RawCircuitGate =>
    (actualCircuitDirective curve points input curveInputMac pointInputMac first.1).table
  let gates := circuitRawGatePrescription keys slopes lifts tables
  let index := fixedKeyIndex (rawCircuitLocation first.1) (rawCircuitWindow first.1) first.2
  let firstUse : RawBucketUse gates index := ⟨first, rfl⟩
  let secondUse : RawBucketUse gates index := ⟨second, indices.symm⟩
  have equal : firstUse = secondUse :=
    circuitRawBucketTweak_injective keys slopes lifts tables index tweaks
  exact congrArg Subtype.val equal

/-- Every actual gate slot has one distinct programming record. -/
theorem actualCircuitSlotRecord_injective
    (curve : CurveGateRequest) (points : PointGateRequests) (input : AffineInput)
    (curveInputMac pointInputMac : InputMac) :
    Function.Injective (fun use : RawCircuitGate × Pipeline.FixedKeySlot =>
      (actualCircuitDirective curve points input curveInputMac pointInputMac use.1).slotRecord use.2) := by
  intro first second same
  exact @actualCircuitSlotDomain_injective curve points input curveInputMac pointInputMac
    first second (congrArg (fun record => (record.index, record.domain)) same)

/-- Every actual circuit directive has one raw gate index. -/
theorem actualCircuitDirective_injective
    (curve : CurveGateRequest) (points : PointGateRequests) (input : AffineInput)
    (curveInputMac pointInputMac : InputMac) :
    Function.Injective (actualCircuitDirective curve points input curveInputMac pointInputMac) := by
  intro first second same
  have records := congrArg (fun directive : GateDirective => directive.slotRecord (.hash 0)) same
  have indices := @actualCircuitSlotRecord_injective curve points input curveInputMac pointInputMac
    (first, .hash 0) (second, .hash 0) records
  exact congrArg Prod.fst indices

/-- The actual complete schedule never repeats a directive. -/
theorem pipelineGateSchedule_nodup
    (curve : CurveGateRequest) (points : PointGateRequests) (input : AffineInput)
    (curveInputMac pointInputMac : InputMac) :
    (pipelineGateSchedule curve points input curveInputMac pointInputMac).Nodup := by
  apply nodup_of_enumerates _ (actualCircuitDirective curve points input curveInputMac pointInputMac)
    (actualCircuitDirective_injective curve points input curveInputMac pointInputMac)
  · exact mem_pipelineGateSchedule_iff curve points input curveInputMac pointInputMac
  · rw [pipelineGateSchedule_length_value, rawCircuitGate_card]

private theorem directiveSlotRecord_injective (directive : GateDirective) :
    Function.Injective directive.slotRecord := by
  intro first second same
  exact congrArg (fun record => record.index.slot) same

/-- Every directive programs each selected slot once. -/
theorem GateDirective.programRecords_nodup (directive : GateDirective) :
    directive.programRecords.Nodup := by
  unfold GateDirective.programRecords
  cases selected : directive.bit
  ·
    change ([.hash 2, .hash 1, .hash 0].map directive.slotRecord).Nodup
    apply List.Nodup.map (directiveSlotRecord_injective directive)
    decide
  ·
    change ([.pad 1, .pad 0].map directive.slotRecord).Nodup
    apply List.Nodup.map (directiveSlotRecord_injective directive)
    decide

/-- The actual complete programming list never repeats a record. -/
theorem pipelineGateProgramRecords_nodup
    (curve : CurveGateRequest) (points : PointGateRequests) (input : AffineInput)
    (curveInputMac pointInputMac : InputMac) :
    (gateProgramRecords (pipelineGateSchedule curve points input curveInputMac pointInputMac)).Nodup := by
  rw [gateProgramRecords, List.nodup_flatMap]
  constructor
  · intro directive _
    exact List.nodup_reverse.mpr directive.programRecords_nodup
  · apply (pipelineGateSchedule_nodup curve points input curveInputMac pointInputMac).pairwise_of_forall_ne
    intro first firstMember second secondMember different
    apply List.disjoint_left.mpr
    intro record firstRecord secondRecord
    rcases (mem_pipelineGateSchedule_iff curve points input curveInputMac pointInputMac first).mp
      firstMember with ⟨firstGate, rfl⟩
    rcases (mem_pipelineGateSchedule_iff curve points input curveInputMac pointInputMac second).mp
      secondMember with ⟨secondGate, rfl⟩
    rcases (GateDirective.mem_programRecords_iff _ record).mp (List.mem_reverse.mp firstRecord) with
      ⟨firstSlot, _, firstSame⟩
    rcases (GateDirective.mem_programRecords_iff _ record).mp (List.mem_reverse.mp secondRecord) with
      ⟨secondSlot, _, secondSame⟩
    have same := @actualCircuitSlotRecord_injective curve points input curveInputMac pointInputMac
      (firstGate, firstSlot) (secondGate, secondSlot) (firstSame.trans secondSame.symm)
    exact different (congrArg (actualCircuitDirective curve points input curveInputMac pointInputMac)
      (congrArg Prod.fst same))

private theorem actualCircuitSlotRecord_rawRange
    (curve : CurveGateRequest) (points : PointGateRequests) (input : AffineInput)
    (curveInputMac pointInputMac : InputMac)
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot)
    (recordEqual : (actualCircuitDirective curve points input curveInputMac pointInputMac gate).slotRecord slot =
      (circuitRawGatePrescription keys slopes lifts tables gate).slotRecord slot) :
    ((actualCircuitDirective curve points input curveInputMac pointInputMac gate).slotRecord slot).range =
      ((circuitRawGatePrescription keys slopes lifts tables gate).offset slot ^^^
          (rawCircuitLocation gate).tweak) ^^^
        (actualCircuitDirective curve points input curveInputMac pointInputMac gate).label := by
  have domains := congrArg PermutationRecord.domain recordEqual
  change (actualCircuitDirective curve points input curveInputMac pointInputMac gate).label ^^^
      (actualCircuitDirective curve points input curveInputMac pointInputMac gate).location.tweak =
    (circuitRawGatePrescription keys slopes lifts tables gate).label slot ^^^
      (rawCircuitLocation gate).tweak at domains
  rw [actualCircuitDirective_location] at domains
  have labelEqual : (circuitRawGatePrescription keys slopes lifts tables gate).label slot =
      (actualCircuitDirective curve points input curveInputMac pointInputMac gate).label := by
    have cancelled := congrArg (fun value => value ^^^ (rawCircuitLocation gate).tweak) domains
    simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using cancelled.symm
  have ranges := congrArg PermutationRecord.range recordEqual
  change _ = (circuitRawGatePrescription keys slopes lifts tables gate).offset slot ^^^
    ((circuitRawGatePrescription keys slopes lifts tables gate).label slot ^^^
      (rawCircuitLocation gate).tweak) at ranges
  rw [labelEqual] at ranges
  rw [BitVec.xor_assoc, BitVec.xor_comm (rawCircuitLocation gate).tweak]
  exact ranges

/-- Distinct raw offsets give the actual pairwise fresh programming list. -/
theorem pipelineGateProgramRecords_pairwise
    (curve : CurveGateRequest) (points : PointGateRequests) (input : AffineInput)
    (curveInputMac pointInputMac : InputMac)
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (recordLaw : ∀ gate slot,
      rawSlotBranch slot =
        (actualCircuitDirective curve points input curveInputMac pointInputMac gate).bit →
      (actualCircuitDirective curve points input curveInputMac pointInputMac gate).slotRecord slot =
        (circuitRawGatePrescription keys slopes lifts tables gate).slotRecord slot)
    (offsetsDistinct : ∀ index, Function.Injective
      (rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index)) :
    (gateProgramRecords (pipelineGateSchedule curve points input curveInputMac pointInputMac)).Pairwise
      (fun first second => first.index = second.index →
        first.domain ≠ second.domain ∧ first.range ≠ second.range) := by
  apply (pipelineGateProgramRecords_nodup curve points input curveInputMac pointInputMac).pairwise_of_forall_ne
  intro first firstMember second secondMember different sameIndex
  rcases (mem_pipelineGateProgramRecords_iff curve points input curveInputMac pointInputMac first).mp
    firstMember with ⟨firstGate, firstSlot, firstActive, rfl⟩
  rcases (mem_pipelineGateProgramRecords_iff curve points input curveInputMac pointInputMac second).mp
    secondMember with ⟨secondGate, secondSlot, secondActive, rfl⟩
  constructor
  · intro sameDomain
    have same := @actualCircuitSlotDomain_injective curve points input curveInputMac pointInputMac
      (firstGate, firstSlot) (secondGate, secondSlot) (Prod.ext sameIndex sameDomain)
    exact different (congrArg (fun use : RawCircuitGate × Pipeline.FixedKeySlot =>
      (actualCircuitDirective curve points input curveInputMac pointInputMac use.1).slotRecord use.2) same)
  · intro sameRange
    have indices : fixedKeyIndex (rawCircuitLocation firstGate) (rawCircuitWindow firstGate) firstSlot =
        fixedKeyIndex (rawCircuitLocation secondGate) (rawCircuitWindow secondGate) secondSlot :=
      (actualCircuitDirective_slotRecord_index curve points input curveInputMac pointInputMac
        firstGate firstSlot).symm.trans (sameIndex.trans
        (actualCircuitDirective_slotRecord_index curve points input curveInputMac pointInputMac
          secondGate secondSlot))
    rw [actualCircuitSlotRecord_rawRange curve points input curveInputMac pointInputMac keys slopes
      lifts tables firstGate firstSlot (recordLaw firstGate firstSlot firstActive),
      actualCircuitSlotRecord_rawRange curve points input curveInputMac pointInputMac keys slopes
        lifts tables secondGate secondSlot (recordLaw secondGate secondSlot secondActive),
      actualCircuitDirective_label curve points input curveInputMac pointInputMac firstGate firstSlot,
      actualCircuitDirective_label curve points input curveInputMac pointInputMac secondGate secondSlot,
      indices] at sameRange
    have offsetEqual :
        (circuitRawGatePrescription keys slopes lifts tables firstGate).offset firstSlot ^^^
          (rawCircuitLocation firstGate).tweak =
        (circuitRawGatePrescription keys slopes lifts tables secondGate).offset secondSlot ^^^
          (rawCircuitLocation secondGate).tweak := by
      have cancelled := congrArg (fun value => value ^^^ circuitBucketInputLabel curveInputMac pointInputMac
        (rawLabelBucket (fixedKeyIndex (rawCircuitLocation secondGate) (rawCircuitWindow secondGate) secondSlot)))
        sameRange
      simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using cancelled
    let gates := circuitRawGatePrescription keys slopes lifts tables
    let index := fixedKeyIndex (rawCircuitLocation firstGate) (rawCircuitWindow firstGate) firstSlot
    let firstUse : RawBucketUse gates index := ⟨(firstGate, firstSlot), rfl⟩
    let secondUse : RawBucketUse gates index := ⟨(secondGate, secondSlot), indices.symm⟩
    have same : firstUse = secondUse := offsetsDistinct index offsetEqual
    exact different (congrArg (fun use : RawBucketUse gates index =>
      (actualCircuitDirective curve points input curveInputMac pointInputMac use.1.1).slotRecord use.1.2) same)

/-- The raw conditions prove the exact fresh-record predicate. -/
theorem pipelineGateProgramRecords_fresh (state : SimulatorState)
    (curve : CurveGateRequest) (points : PointGateRequests) (input : AffineInput)
    (curveInputMac pointInputMac : InputMac)
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (recordLaw : ∀ gate slot,
      rawSlotBranch slot =
        (actualCircuitDirective curve points input curveInputMac pointInputMac gate).bit →
      (actualCircuitDirective curve points input curveInputMac pointInputMac gate).slotRecord slot =
        (circuitRawGatePrescription keys slopes lifts tables gate).slotRecord slot)
    (offsetsDistinct : ∀ index, Function.Injective
      (rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index))
    (fresh : ∀ gate slot,
      rawSlotBranch slot =
        (actualCircuitDirective curve points input curveInputMac pointInputMac gate).bit →
      let record := (circuitRawGatePrescription keys slopes lifts tables gate).slotRecord slot
      FreshPermutationPair state.fixedTranscript record.index record.domain record.range) :
    FreshRecordSchedule state.fixedTranscript
      (gateProgramRecords (pipelineGateSchedule curve points input curveInputMac pointInputMac)) := by
  apply freshRecordSchedule_of_pairwise
  · intro record member
    rcases (mem_pipelineGateProgramRecords_iff curve points input curveInputMac pointInputMac record).mp
      member with ⟨gate, slot, active, rfl⟩
    rw [recordLaw gate slot active]
    exact fresh gate slot active
  · exact pipelineGateProgramRecords_pairwise curve points input curveInputMac pointInputMac
      keys slopes lifts tables recordLaw offsetsDistinct

/-- The actual schedule preserves its bad flag under the raw freshness conditions. -/
theorem programPipelineGateSchedule_bad_eq_of_rawFresh (state : SimulatorState)
    (curve : CurveGateRequest) (points : PointGateRequests) (input : AffineInput)
    (curveInputMac pointInputMac : InputMac)
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (recordLaw : ∀ gate slot,
      rawSlotBranch slot =
        (actualCircuitDirective curve points input curveInputMac pointInputMac gate).bit →
      (actualCircuitDirective curve points input curveInputMac pointInputMac gate).slotRecord slot =
        (circuitRawGatePrescription keys slopes lifts tables gate).slotRecord slot)
    (offsetsDistinct : ∀ index, Function.Injective
      (rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index))
    (fresh : ∀ gate slot,
      rawSlotBranch slot =
        (actualCircuitDirective curve points input curveInputMac pointInputMac gate).bit →
      let record := (circuitRawGatePrescription keys slopes lifts tables gate).slotRecord slot
      FreshPermutationPair state.fixedTranscript record.index record.domain record.range) :
    (programGateSchedule state (pipelineGateSchedule curve points input curveInputMac pointInputMac)).bad =
      state.bad := by
  exact programGateSchedule_bad_eq_of_freshRecords state _
    (pipelineGateProgramRecords_fresh state curve points input curveInputMac pointInputMac
      keys slopes lifts tables recordLaw offsetsDistinct fresh)

/-- The actual source proves the exact fresh-record predicate. -/
theorem circuitMaskSchedule_fresh
    (state : SimulatorState) (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows)
    (input : AffineInput) (source : CircuitMaskSample) (curveKey pointKey : InputMacKey)
    (offsetsDistinct : ∀ index, Function.Injective
      (rawBucketOffset (sourceGatePrescription source pointKey curveKey
        (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))) index))
    (fresh : ∀ gate slot,
      rawSlotBranch slot = circuitBucketInputBit input
        (rawLabelBucket (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) →
      let record := (sourceGatePrescription source pointKey curveKey
        (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)) gate).slotRecord slot
      FreshPermutationPair state.fixedTranscript record.index record.domain record.range) :
    let sample := circuitMaskSampleGarble bridgeKey mask rows input source
    FreshRecordSchedule state.fixedTranscript (gateProgramRecords
      (pipelineGateSchedule sample.curveRequest sample.pointRequests input
        (curveKey.encodeAffine input) (pointKey.encodeAffine input))) := by
  dsimp only
  apply pipelineGateProgramRecords_fresh state _ _ input
    (curveKey.encodeAffine input) (pointKey.encodeAffine input)
    (circuitGateKey pointKey curveKey) (circuitSourceSlope source)
    (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
    (circuitSourceTable source)
  · exact fun gate slot active => circuitMaskDirective_record_eq_raw bridgeKey mask rows input source
      curveKey pointKey gate slot active
  · exact offsetsDistinct
  · intro gate slot active
    apply fresh gate slot
    exact active.trans (actualCircuitDirective_bit _ _ input _ _ gate slot)

/-- The actual mask source supplies the selected record law for freshness. -/
theorem programCircuitMaskSchedule_bad_eq_of_rawFresh
    (state : SimulatorState) (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows)
    (input : AffineInput) (source : CircuitMaskSample) (curveKey pointKey : InputMacKey)
    (offsetsDistinct : ∀ index, Function.Injective
      (rawBucketOffset (sourceGatePrescription source pointKey curveKey
        (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))) index))
    (fresh : ∀ gate slot,
      rawSlotBranch slot = circuitBucketInputBit input
        (rawLabelBucket (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) →
      let record := (sourceGatePrescription source pointKey curveKey
        (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)) gate).slotRecord slot
      FreshPermutationPair state.fixedTranscript record.index record.domain record.range) :
    let sample := circuitMaskSampleGarble bridgeKey mask rows input source
    (programGateSchedule state (pipelineGateSchedule sample.curveRequest sample.pointRequests input
      (curveKey.encodeAffine input) (pointKey.encodeAffine input))).bad = state.bad := by
  exact programGateSchedule_bad_eq_of_freshRecords state _
    (circuitMaskSchedule_fresh state bridgeKey mask rows input source curveKey pointKey offsetsDistinct fresh)

end Kriterion.ArgoMAC.Security
