import Proof.Privacy.Source.SharedRawAssembly

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 2048
attribute [local instance] instFintypeRawCircuitGate_1

/-- This type retains the selected branch in one shared slot. -/
def SharedActiveRole (slot : Fin 3) (selected : Bool) :=
  {role : SharedSlotRole slot // rawSlotBranch role.1 = selected}

instance sharedActiveRoleFintype (slot : Fin 3) (selected : Bool) :
    Fintype (SharedActiveRole slot selected) := by
  unfold SharedActiveRole
  infer_instance

/-- Each selected branch uses one role in slots zero and one. -/
theorem sharedActiveRole_card (slot : Fin 3) (selected : Bool) :
    Fintype.card (SharedActiveRole slot selected) =
      if slot.val < 2 ∨ selected = false then 1 else 0 := by
  cases selected <;> fin_cases slot <;> decide

/-- This type retains actual source records in one selected branch. -/
def SharedActiveUse {Gate : Type} (gates : Gate → RawGatePrescription)
    (index : Shared.FixedKeyIndex) (selected : Bool) :=
  {use : SharedRawBucketUse gates index // rawSlotBranch use.1.2 = selected}

instance sharedActiveUseFintype {Gate : Type} [Fintype Gate]
    (gates : Gate → RawGatePrescription) (index : Shared.FixedKeyIndex) (selected : Bool) :
    Fintype (SharedActiveUse gates index selected) := by
  unfold SharedActiveUse
  infer_instance

/-- The actual active records split into one role and the complete row set. -/
def sharedActiveUseEquiv
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (index : Shared.FixedKeyIndex) (selected : Bool) :
    SharedActiveUse (circuitRawGatePrescription keys slopes lifts tables) index selected ≃
      SharedActiveRole index.slot selected ×
        Fin (circuitBucketSize ⟨index.kind, index.position, .hash 0⟩) where
  toFun use :=
    let listed := sharedCircuitBucketListEquiv keys slopes lifts tables index use.1
    (⟨listed.1, use.2⟩, listed.2)
  invFun listed :=
    ⟨(sharedCircuitBucketListEquiv keys slopes lifts tables index).symm (listed.1.1, listed.2), listed.1.2⟩
  left_inv use := by
    apply Subtype.ext
    exact (sharedCircuitBucketListEquiv keys slopes lifts tables index).symm_apply_apply use.1
  right_inv listed := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst
        ((sharedCircuitBucketListEquiv keys slopes lifts tables index).apply_symm_apply (listed.1.1, listed.2))
    · change ((sharedCircuitBucketListEquiv keys slopes lifts tables index)
        ((sharedCircuitBucketListEquiv keys slopes lifts tables index).symm (listed.1.1, listed.2))).2 = listed.2
      exact congrArg Prod.snd
        ((sharedCircuitBucketListEquiv keys slopes lifts tables index).apply_symm_apply (listed.1.1, listed.2))

/-- This count includes all active records in the actual three-slot circuit. -/
theorem sharedActiveUse_card
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (index : Shared.FixedKeyIndex) (selected : Bool) :
    Fintype.card (SharedActiveUse (circuitRawGatePrescription keys slopes lifts tables) index selected) =
      (if index.slot.val < 2 ∨ selected = false then 1 else 0) *
        circuitBucketSize ⟨index.kind, index.position, .hash 0⟩ := by
  rw [Fintype.card_congr (sharedActiveUseEquiv keys slopes lifts tables index selected),
    Fintype.card_prod, sharedActiveRole_card, Fintype.card_fin]

end
end Kriterion.ArgoMAC.Security
