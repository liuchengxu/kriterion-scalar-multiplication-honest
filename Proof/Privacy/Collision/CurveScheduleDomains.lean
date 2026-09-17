import Proof.Privacy.Programming.ActualScheduleRecords
import Proof.Privacy.Collision.PartialInactiveCount
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography

theorem mem_curveGateProgramRecords_iff (curve : CurveGateRequest)
    (input : AffineInput) (curveMac : InputMac)
    (record : PermutationRecord Pipeline.FixedKeyIndex Block) :
    record ∈ gateProgramRecords (curve.schedule input curveMac) ↔
      ∃ adaptor bit slot,
        rawSlotBranch slot = (curve.actualDirective input curveMac adaptor bit).bit ∧
        (curve.actualDirective input curveMac adaptor bit).slotRecord slot = record := by
  simp only [gateProgramRecords, List.mem_flatMap, List.mem_reverse,
    CurveGateRequest.mem_schedule_iff, GateDirective.mem_programRecords_iff]
  constructor
  · rintro ⟨directive, ⟨adaptor, bit, rfl⟩, slot, active, same⟩
    exact ⟨adaptor, bit, slot, active, same⟩
  · rintro ⟨adaptor, bit, slot, active, same⟩
    exact ⟨_, ⟨adaptor, bit, rfl⟩, slot, active, same⟩

def isCurveIndex (index : Pipeline.FixedKeyIndex) : Prop :=
  match index.kind with
  | .curve _ => True
  | .point _ _ => False

private theorem rawIndex_isCurve (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot) :
    isCurveIndex (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot) ↔
      ∃ adaptor bit, gate = .inl (adaptor, bit) := by
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · simp [isCurveIndex, fixedKeyIndex, rawCircuitLocation, Pipeline.FixedKeyLocation.kind]
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;>
      simp [isCurveIndex, fixedKeyIndex, rawCircuitLocation, Pipeline.FixedKeyLocation.kind]

theorem curveGateProgramRecords_filter (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveMac pointMac : InputMac)
    (record : PermutationRecord Pipeline.FixedKeyIndex Block) :
    record ∈ gateProgramRecords (curve.schedule input curveMac) ↔
      record ∈ gateProgramRecords (pipelineGateSchedule curve points input curveMac pointMac) ∧
        isCurveIndex record.index := by
  rw [mem_curveGateProgramRecords_iff, mem_pipelineGateProgramRecords_iff]
  constructor
  · rintro ⟨adaptor, bit, slot, active, rfl⟩
    refine ⟨⟨.inl (adaptor, bit), slot, active, rfl⟩, ?_⟩
    change isCurveIndex ((actualCircuitDirective curve points input curveMac pointMac
      (.inl (adaptor, bit))).slotRecord slot).index
    rw [actualCircuitDirective_slotRecord_index]
    exact (rawIndex_isCurve _ _).mpr ⟨adaptor, bit, rfl⟩
  · rintro ⟨⟨gate, slot, active, rfl⟩, curveIndex⟩
    rw [actualCircuitDirective_slotRecord_index] at curveIndex
    rcases (rawIndex_isCurve gate slot).mp curveIndex with ⟨adaptor, bit, rfl⟩
    exact ⟨adaptor, bit, slot, active, rfl⟩

attribute [local instance] Classical.propDecidable

theorem curveGateProgramRecords_domains_filter
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveMac pointMac : InputMac)
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (index : Pipeline.FixedKeyIndex) :
    {domain | ∃ record ∈ gateProgramRecords (curve.schedule input curveMac),
      record.index = index ∧ record.domain = domain} =
      if isCurveIndex index then
        rawActiveDomains (circuitRawGatePrescription keys slopes lifts tables)
          (circuitBucketInputBit input) (circuitBucketInputLabel curveMac pointMac) index
      else ∅ := by
  classical
  rw [← pipelineGateProgramRecords_domains curve points input curveMac pointMac keys slopes lifts tables]
  ext domain
  simp only [Set.mem_setOf_eq, curveGateProgramRecords_filter curve points input curveMac pointMac]
  by_cases curveIndex : isCurveIndex index
  · rw [if_pos curveIndex]
    constructor
    · rintro ⟨record, ⟨member, _⟩, sameIndex, sameDomain⟩
      exact ⟨record, member, sameIndex, sameDomain⟩
    · rintro ⟨record, member, sameIndex, sameDomain⟩
      exact ⟨record, ⟨member, sameIndex ▸ curveIndex⟩, sameIndex, sameDomain⟩
  · rw [if_neg curveIndex]
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨record, ⟨_, curveRecord⟩, sameIndex, _⟩
    exact curveIndex (sameIndex ▸ curveRecord)

attribute [local instance] fixedQueryDomainFintype

theorem curveGateProgramRecords_domainCount [Fintype Block]
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveMac pointMac : InputMac)
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (index : Pipeline.FixedKeyIndex) :
    Fintype.card (FixedQueryDomain (gateProgramRecords (curve.schedule input curveMac)) index) =
      if isCurveIndex index ∧
        rawSlotBranch index.slot = circuitBucketInputBit input (rawLabelBucket index)
      then circuitBucketSize index else 0 := by
  classical
  have domains := curveGateProgramRecords_domains_filter curve points input curveMac pointMac
    keys slopes lifts tables index
  by_cases curveIndex : isCurveIndex index
  · rw [if_pos curveIndex, ← pipelineGateProgramRecords_domains curve points input curveMac
      pointMac keys slopes lifts tables index] at domains
    have equivalence : FixedQueryDomain (gateProgramRecords (curve.schedule input curveMac)) index ≃
        FixedQueryDomain (gateProgramRecords (pipelineGateSchedule curve points input curveMac pointMac)) index :=
      Equiv.setCongr domains
    have count := Fintype.card_congr equivalence
    rw [count, pipelineGateProgramRecords_domainCount curve points input curveMac pointMac
      keys slopes lifts tables index]
    simp only [curveIndex, true_and]
  · rw [if_neg curveIndex] at domains
    letI : IsEmpty (FixedQueryDomain (gateProgramRecords (curve.schedule input curveMac)) index) :=
      ⟨fun value => by
        have member := value.property
        change value.val ∈ {domain | ∃ record ∈ gateProgramRecords (curve.schedule input curveMac),
          record.index = index ∧ record.domain = domain} at member
        rw [domains] at member
        exact member⟩
    simp only [Fintype.card_of_isEmpty, curveIndex, false_and, if_false]

/-- The invalid schedule programs exactly the exposed curve domains. -/
theorem curveGateProgramRecords_domains
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveMac pointMac : InputMac)
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (index : Pipeline.FixedKeyIndex) :
    {domain | ∃ record ∈ gateProgramRecords (curve.schedule input curveMac),
      record.index = index ∧ record.domain = domain} =
      partialActiveDomains (circuitRawGatePrescription keys slopes lifts tables)
        (curveOnlyExposed (circuitBucketInputBit input))
        (fun bucket _ => circuitBucketInputLabel curveMac pointMac bucket) index := by
  rw [curveGateProgramRecords_domains_filter curve points input curveMac pointMac keys slopes lifts tables]
  rcases index with ⟨kind, bit, slot⟩
  cases kind <;>
    simp [isCurveIndex, partialActiveDomains, curveOnlyExposed, rawActiveDomains, rawLabelBucket]
  split_ifs <;> simp_all

/-- The invalid schedule writes one domain in each selected curve bucket. -/
theorem curveGateProgramRecords_exposedCount [Fintype Block]
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveMac pointMac : InputMac)
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (index : Pipeline.FixedKeyIndex) :
    Fintype.card (FixedQueryDomain (gateProgramRecords (curve.schedule input curveMac)) index) =
      if curveOnlyExposed (circuitBucketInputBit input) (rawLabelBucket index) (rawSlotBranch index.slot)
      then circuitBucketSize index else 0 := by
  rw [curveGateProgramRecords_domainCount curve points input curveMac pointMac keys slopes lifts tables]
  rcases index with ⟨kind, bit, slot⟩
  cases kind <;> simp [isCurveIndex, curveOnlyExposed, rawLabelBucket]
  split_ifs <;> simp_all

end Kriterion.ArgoMAC.Security
