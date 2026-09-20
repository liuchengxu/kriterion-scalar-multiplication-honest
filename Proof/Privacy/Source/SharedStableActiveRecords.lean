import Proof.Privacy.Source.SharedStableDomains

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 2048

/-- A fixed simulator target source gives the same active record for all unused labels. -/
theorem active_record_stable (context : Context) (hidden : HiddenPublicSample)
    (first second : EncPRF.PermutationIndex → Block) (gate : RawCircuitGate)
    (slot : Pipeline.FixedKeySlot)
    (active : rawSlotBranch slot = inputSelectedLabelBit context.input (circuitGateWire gate)) :
    (context.gates (hidden, first) gate).slotRecord slot =
      (context.gates (hidden, second) gate).slotRecord slot := by
  have labels := active_label_stable context (hidden, first) (hidden, second) gate slot active
  have offsets : (context.gates (hidden, first) gate).offset slot =
      (context.gates (hidden, second) gate).offset slot := by
    rw [raw_gate_offset, raw_gate_offset]
  have firstLocation : (context.gates (hidden, first) gate).location = rawCircuitLocation gate := rfl
  have secondLocation : (context.gates (hidden, second) gate).location = rawCircuitLocation gate := rfl
  have firstWindow : (context.gates (hidden, first) gate).window = rawCircuitWindow gate := rfl
  have secondWindow : (context.gates (hidden, second) gate).window = rawCircuitWindow gate := rfl
  unfold RawGatePrescription.slotRecord
  rw [labels, offsets, firstLocation, secondLocation, firstWindow, secondWindow]

/-- The active raw record premise matches the source mass interface. -/
theorem active_records_compatible (context : Context) (hidden : HiddenPublicSample)
    (anchor labels : EncPRF.PermutationIndex → Block)
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (compatible : ∀ gate slot,
      rawSlotBranch slot = inputSelectedLabelBit context.input (circuitGateWire gate) →
      let record := (context.gates (hidden, anchor) gate).slotRecord slot
      reference.permutation (Shared.fixedIndex record.index) record.domain = record.range)
    (index : Shared.FixedKeyIndex)
    (use : SharedActiveUse (context.gates (hidden, labels)) index (sharedCircuitSelected context.input index)) :
    reference.permutation index (sharedRawBucketDomain (context.gates (hidden, labels)) index use.1) =
      sharedRawBucketRange (context.gates (hidden, labels)) index use.1 := by
  have indexed : Shared.fixedIndex
      (fixedKeyIndex (rawCircuitLocation use.1.1.1) (rawCircuitWindow use.1.1.1) use.1.1.2) = index := use.1.2
  have wire := (congrArg (sharedCircuitSelected context.input) indexed).symm.trans
    (sharedCircuitSelected_wire context.input use.1.1.1 use.1.1.2)
  have selected := use.2.trans wire
  have result := compatible use.1.1.1 use.1.1.2 selected
  dsimp only at result
  rw [active_record_stable context hidden anchor labels use.1.1.1 use.1.1.2 selected] at result
  change reference.permutation (Shared.fixedIndex (fixedKeyIndex _ _ use.1.1.2)) _ = _ at result
  rw [use.1.2] at result
  exact result

end
end Kriterion.ArgoMAC.Security.SharedRetained
