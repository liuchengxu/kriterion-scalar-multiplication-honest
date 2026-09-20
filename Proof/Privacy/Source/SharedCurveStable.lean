import Proof.Privacy.Collision.SharedCurveHiddenLabels
import Proof.Privacy.Source.SharedStableActiveRecords

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography
noncomputable section
attribute [local irreducible] Context.source Context.lifts

/-- A curve bucket contains only curve gates. -/
theorem curveGate_of_sharedSlot (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot)
    (curve : sharedCurveSlot (Shared.fixedIndex
      (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) = true) :
    ∃ adaptor position, gate = .inl (adaptor, position) := by
  rcases gate with ⟨adaptor, position⟩ | ⟨row, family⟩
  · exact ⟨adaptor, position, rfl⟩
  · rcases family with ⟨adaptor, position⟩ | (⟨adaptor, position⟩ | ⟨adaptor, position⟩) <;>
      simp only [sharedCurveSlot, Shared.fixedIndex, fixedKeyIndex, rawCircuitLocation,
        Pipeline.FixedKeyLocation.kind, Bool.false_eq_true] at curve

/-- A selected curve label is independent of both hidden label arrays. -/
theorem curveHidden_active_label (context : Context) (hidden : HiddenPublicSample)
    (first second : InputMacKey) (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot)
    (curve : sharedCurveSlot (Shared.fixedIndex
      (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) = true)
    (active : rawSlotBranch slot = inputSelectedLabelBit context.input (circuitGateWire gate)) :
    ((context.curveHidden first).gates (hidden, curveUnused first) gate).label slot =
      ((context.curveHidden second).gates (hidden, curveUnused second) gate).label slot := by
  rw [raw_gate_label, raw_gate_label]
  obtain ⟨adaptor, position, rfl⟩ := curveGate_of_sharedSlot gate slot curve
  simp only [Context.gateLabel, Context.curveHidden, active, if_true]

/-- The hidden label arrays do not change the source masks or ciphertexts. -/
theorem curveHidden_source_eq (context : Context) (key : InputMacKey) (hidden : HiddenPublicSample) :
    (context.curveHidden key).source hidden = context.source hidden := by
  unfold Context.source Context.curveHidden
  rfl

/-- The hidden label arrays do not change the source hash lifts. -/
theorem curveHidden_lifts_eq (context : Context) (key : InputMacKey) (hidden : HiddenPublicSample) :
    (context.curveHidden key).lifts hidden = context.lifts hidden := by
  unfold Context.lifts
  rw [curveHidden_source_eq]

/-- A selected curve record is independent of both hidden label arrays. -/
theorem curveHidden_active_record (context : Context) (hidden : HiddenPublicSample)
    (first second : InputMacKey) (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot)
    (curve : sharedCurveSlot (Shared.fixedIndex
      (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) = true)
    (active : rawSlotBranch slot = inputSelectedLabelBit context.input (circuitGateWire gate)) :
    (((context.curveHidden first).gates (hidden, curveUnused first) gate).slotRecord slot) =
      (((context.curveHidden second).gates (hidden, curveUnused second) gate).slotRecord slot) := by
  have labels := curveHidden_active_label context hidden first second gate slot curve active
  have offsets : ((context.curveHidden first).gates (hidden, curveUnused first) gate).offset slot =
      ((context.curveHidden second).gates (hidden, curveUnused second) gate).offset slot := by
    rw [raw_gate_offset, raw_gate_offset, curveHidden_source_eq, curveHidden_source_eq,
      curveHidden_lifts_eq, curveHidden_lifts_eq]
  have firstLocation : ((context.curveHidden first).gates (hidden, curveUnused first) gate).location =
      rawCircuitLocation gate := rfl
  have secondLocation : ((context.curveHidden second).gates (hidden, curveUnused second) gate).location =
      rawCircuitLocation gate := rfl
  have firstWindow : ((context.curveHidden first).gates (hidden, curveUnused first) gate).window =
      rawCircuitWindow gate := rfl
  have secondWindow : ((context.curveHidden second).gates (hidden, curveUnused second) gate).window =
      rawCircuitWindow gate := rfl
  unfold RawGatePrescription.slotRecord
  rw [labels, offsets, firstLocation, secondLocation, firstWindow, secondWindow]

private theorem curveDomain_subset (context : Context) (hidden : HiddenPublicSample)
    (first second : InputMacKey) (index : Shared.FixedKeyIndex) :
    sharedCurveDomains ((context.curveHidden first).gates (hidden, curveUnused first))
      (sharedCircuitSelected context.input) index ⊆
    sharedCurveDomains ((context.curveHidden second).gates (hidden, curveUnused second))
      (sharedCircuitSelected context.input) index := by
  intro domain member
  by_cases curve : sharedCurveSlot index = true
  · change domain ∈ (if sharedCurveSlot index = true then _ else _) at member ⊢
    rw [if_pos curve] at member ⊢
    obtain ⟨use, equal⟩ := member
    let moved : SharedActiveUse ((context.curveHidden second).gates (hidden, curveUnused second))
        index (sharedCircuitSelected context.input index) := ⟨⟨use.1.1, use.1.2⟩, use.2⟩
    refine ⟨moved, ?_⟩
    have indexed : Shared.fixedIndex (fixedKeyIndex (rawCircuitLocation use.1.1.1)
      (rawCircuitWindow use.1.1.1) use.1.1.2) = index := use.1.2
    have selected := use.2.trans ((congrArg (sharedCircuitSelected context.input) indexed).symm.trans
      (sharedCircuitSelected_wire context.input use.1.1.1 use.1.1.2))
    have labelEq := curveHidden_active_label context hidden first second use.1.1.1 use.1.1.2
      (by rw [indexed]; exact curve) selected
    have domainEq : sharedRawBucketDomain ((context.curveHidden first).gates (hidden, curveUnused first)) index use.1 =
        sharedRawBucketDomain ((context.curveHidden second).gates (hidden, curveUnused second)) index moved.1 := by
      change _ ^^^ (rawCircuitLocation use.1.1.1).tweak = _ ^^^ (rawCircuitLocation use.1.1.1).tweak
      exact congrArg (fun label => label ^^^ (rawCircuitLocation use.1.1.1).tweak) labelEq
    exact domainEq.symm.trans equal
  · change domain ∈ (if sharedCurveSlot index = true then _ else _) at member
    rw [if_neg curve] at member
    exact False.elim member

/-- Both hidden arrays preserve the curve-only programmed domain set. -/
theorem curveHidden_domains_stable (context : Context) (hidden : HiddenPublicSample)
    (first second : InputMacKey) :
    sharedCurveDomains ((context.curveHidden first).gates (hidden, curveUnused first))
      (sharedCircuitSelected context.input) =
    sharedCurveDomains ((context.curveHidden second).gates (hidden, curveUnused second))
      (sharedCircuitSelected context.input) := by
  funext index
  exact Set.Subset.antisymm (curveDomain_subset context hidden first second index)
    (curveDomain_subset context hidden second first index)

end
end Kriterion.ArgoMAC.Security.SharedRetained
