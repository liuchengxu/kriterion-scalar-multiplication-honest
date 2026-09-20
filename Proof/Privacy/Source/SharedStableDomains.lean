import Proof.Privacy.Source.SharedRetainedPostquery

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 2048
attribute [local irreducible] Context.source Context.lifts

private def useTransport {Gate : Type} (first second : Gate → RawGatePrescription)
    (locations : ∀ gate, (first gate).location = (second gate).location)
    (windows : ∀ gate, (first gate).window = (second gate).window)
    (index : Shared.FixedKeyIndex) (use : SharedRawBucketUse first index) :
    SharedRawBucketUse second index := ⟨use.1, by
  rw [← locations, ← windows]
  exact use.2⟩

private theorem transported_domain {Gate : Type} (first second : Gate → RawGatePrescription)
    (locations : ∀ gate, (first gate).location = (second gate).location)
    (windows : ∀ gate, (first gate).window = (second gate).window)
    (index : Shared.FixedKeyIndex) (use : SharedRawBucketUse first index)
    (labels : (first use.1.1).label use.1.2 = (second use.1.1).label use.1.2) :
    sharedRawBucketDomain first index use =
      sharedRawBucketDomain second index (useTransport first second locations windows index use) := by
  dsimp only [sharedRawBucketDomain, useTransport]
  rw [locations, labels]

private theorem gates_location (context : Context)
    (first second : HiddenPublicSample × (EncPRF.PermutationIndex → Block)) (gate : RawCircuitGate) :
    (context.gates first gate).location = (context.gates second gate).location := by
  trans rawCircuitLocation gate <;> rfl

private theorem gates_window (context : Context)
    (first second : HiddenPublicSample × (EncPRF.PermutationIndex → Block)) (gate : RawCircuitGate) :
    (context.gates first gate).window = (context.gates second gate).window := by
  trans rawCircuitWindow gate <;> rfl

private theorem gates_index (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block)) (gate : RawCircuitGate)
    (slot : Pipeline.FixedKeySlot) :
    Shared.fixedIndex (fixedKeyIndex (context.gates sample gate).location (context.gates sample gate).window slot) =
      Shared.fixedIndex (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot) := rfl

/-- The selected raw label does not depend on hidden samples. -/
theorem active_label_stable (context : Context)
    (first second : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot)
    (active : rawSlotBranch slot = inputSelectedLabelBit context.input (circuitGateWire gate)) :
    (context.gates first gate).label slot = (context.gates second gate).label slot := by
  rw [raw_gate_label, raw_gate_label]
  cases gate <;> simp only [Context.gateLabel, active, if_true]

/-- Each active domain remains the same after the hidden source changes. -/
theorem active_domain_stable (context : Context)
    (first second : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (index : Shared.FixedKeyIndex)
    (use : SharedActiveUse (context.gates first) index (sharedCircuitSelected context.input index)) :
    sharedRawBucketDomain (context.gates first) index use.1 =
      sharedRawBucketDomain (context.gates second) index (useTransport (context.gates first) (context.gates second)
        (gates_location context first second) (gates_window context first second) index use.1) := by
  have indexed := (gates_index context first use.1.1.1 use.1.1.2).symm.trans use.1.2
  have wire := (congrArg (sharedCircuitSelected context.input) indexed).symm.trans
    (sharedCircuitSelected_wire context.input use.1.1.1 use.1.1.2)
  have selected := use.2.trans wire
  exact transported_domain (context.gates first) (context.gates second)
    (gates_location context first second) (gates_window context first second) index use.1
      (active_label_stable context first second use.1.1.1 use.1.1.2 selected)

private theorem activeDomains_eq {Gate : Type} (first second : Gate → RawGatePrescription)
    (selected : Shared.FixedKeyIndex → Bool)
    (locations : ∀ gate, (first gate).location = (second gate).location)
    (windows : ∀ gate, (first gate).window = (second gate).window)
    (forward : ∀ index, ∀ use : SharedActiveUse first index (selected index),
      sharedRawBucketDomain first index use.1 =
        sharedRawBucketDomain second index (useTransport first second locations windows index use.1))
    (backward : ∀ index, ∀ use : SharedActiveUse second index (selected index),
      sharedRawBucketDomain second index use.1 =
        sharedRawBucketDomain first index (useTransport second first
          (fun gate => (locations gate).symm) (fun gate => (windows gate).symm) index use.1)) :
    sharedActiveDomains first selected = sharedActiveDomains second selected := by
  funext index
  ext domain
  constructor
  · rintro ⟨use, equal⟩
    exact ⟨⟨useTransport _ _ locations windows index use.1, use.2⟩, (forward index use).symm.trans equal⟩
  · rintro ⟨use, equal⟩
    exact ⟨⟨useTransport _ _ (fun gate => (locations gate).symm) (fun gate => (windows gate).symm)
      index use.1, use.2⟩, (backward index use).symm.trans equal⟩

/-- Every retained sample has the same active-domain set. -/
theorem active_domains_stable (context : Context)
    (first second : HiddenPublicSample × (EncPRF.PermutationIndex → Block)) :
    sharedActiveDomains (context.gates first) (sharedCircuitSelected context.input) =
      sharedActiveDomains (context.gates second) (sharedCircuitSelected context.input) := by
  apply activeDomains_eq (context.gates first) (context.gates second)
    (sharedCircuitSelected context.input) (gates_location context first second) (gates_window context first second)
  · exact active_domain_stable context first second
  · exact active_domain_stable context second first

end
end Kriterion.ArgoMAC.Security.SharedRetained
