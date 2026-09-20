import Proof.Privacy.Collision.SharedCrossBranchBound

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 2048

/-- This equivalence lists the actual shared range slots for one input coordinate. -/
def pointFamilySlotEquiv (coordinate : EncPRF.Coordinate) :
    ({family : PointGateFamily // family.coordinate = coordinate} × Fin 2) ≃
      Fin (pointSharedSlotCount coordinate) :=
  (Fintype.equivFin _).trans (finCongr (pointSharedSlotCount_actual coordinate))

/-- The input bit selects the hash role or the pad role in a shared slot. -/
def sharedBranchRole (selected : Bool) (slot : Fin 2) : Pipeline.FixedKeySlot :=
  if selected then .pad slot else .hash slot.castSucc

/-- The grouped data uses the actual source offsets of every point family. -/
def pointSharedBranches
    (visible : Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : AffineInput)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (hidden : Fin FieldMacToECMac.outputMacCount → HiddenRowSample)
    (activeLabels hiddenPads : EncPRF.PermutationIndex → Block)
    (index : EncPRF.PermutationIndex) : SharedPointBranches index.1 := {
  activeLabel := activeLabels index
  hiddenPad := hiddenPads index
  tweak := fun row => BitVec.ofNat 128 row.val
  activeOffset := fun slot row =>
    let use := (pointFamilySlotEquiv index.1).symm slot
    pointBranchOffset row (visible row) (hidden row) (rows row) input (targets row)
      use.1.1 index.2 (sharedBranchRole (inputSelectedLabelBit input index) use.2)
  hiddenOffset := fun slot row =>
    let use := (pointFamilySlotEquiv index.1).symm slot
    pointBranchOffset row (visible row) (hidden row) (rows row) input (targets row)
      use.1.1 index.2 (sharedBranchRole (!(inputSelectedLabelBit input index)) use.2)
}

/-- The grouped offset retains the selected role of each actual point family. -/
theorem pointSharedBranches_activeOffset
    (visible : Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : AffineInput)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (hidden : Fin FieldMacToECMac.outputMacCount → HiddenRowSample)
    (activeLabels hiddenPads : EncPRF.PermutationIndex → Block)
    (family : PointGateFamily) (position : Fin coordinateBitCount)
    (slot : Fin 2) (row : Fin FieldMacToECMac.outputMacCount) :
    (pointSharedBranches visible rows input targets hidden activeLabels hiddenPads
      (family.coordinate, position)).activeOffset
        (pointFamilySlotEquiv family.coordinate (⟨family, rfl⟩, slot)) row =
      pointBranchOffset row (visible row) (hidden row) (rows row) input (targets row)
        family position (sharedBranchRole (family.selectedBit input position) slot) := by
  simp only [pointSharedBranches, Equiv.symm_apply_apply, ← PointGateFamily.selectedBit_coordinate]

/-- The grouped offset also retains the unused role of each actual point family. -/
theorem pointSharedBranches_hiddenOffset
    (visible : Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : AffineInput)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (hidden : Fin FieldMacToECMac.outputMacCount → HiddenRowSample)
    (activeLabels hiddenPads : EncPRF.PermutationIndex → Block)
    (family : PointGateFamily) (position : Fin coordinateBitCount)
    (slot : Fin 2) (row : Fin FieldMacToECMac.outputMacCount) :
    (pointSharedBranches visible rows input targets hidden activeLabels hiddenPads
      (family.coordinate, position)).hiddenOffset
        (pointFamilySlotEquiv family.coordinate (⟨family, rfl⟩, slot)) row =
      pointBranchOffset row (visible row) (hidden row) (rows row) input (targets row)
        family position (sharedBranchRole (!(family.selectedBit input position)) slot) := by
  simp only [pointSharedBranches, Equiv.symm_apply_apply, ← PointGateFamily.selectedBit_coordinate]

/-- A good row sample gives distinct offsets in every grouped point role. -/
theorem pointSharedBranches_offsets_injective
    (visible : Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : AffineInput)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (hidden : Fin FieldMacToECMac.outputMacCount → HiddenRowSample)
    (activeLabels hiddenPads : EncPRF.PermutationIndex → Block)
    (good : ¬ pointBranchCollision visible rows input targets hidden)
    (index : EncPRF.PermutationIndex) (slot : Fin (pointSharedSlotCount index.1)) :
    Function.Injective ((pointSharedBranches visible rows input targets hidden
      activeLabels hiddenPads index).activeOffset slot) ∧
    Function.Injective ((pointSharedBranches visible rows input targets hidden
      activeLabels hiddenPads index).hiddenOffset slot) := by
  constructor <;> exact pointBranchCollision_false_injective visible rows input targets hidden good _ _ _

/-- The paper's 91 digit tweaks have no repetitions. -/
theorem pointSharedBranches_tweaks_injective :
    Function.Injective (fun row : Fin FieldMacToECMac.outputMacCount => BitVec.ofNat 128 row.val) := by
  intro first second equal
  have numeric := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat] at numeric
  have rowCount : FieldMacToECMac.outputMacCount = 91 := rfl
  have firstBound : first.val < 2 ^ 128 := by have := first.isLt; omega
  have secondBound : second.val < 2 ^ 128 := by have := second.isLt; omega
  rw [Nat.mod_eq_of_lt firstBound, Nat.mod_eq_of_lt secondBound] at numeric
  exact Fin.ext numeric

/-- A retained coordinate label separates both actual point branches in each shared slot. -/
theorem pointSharedBranches_assignments_injective
    (visible : Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : AffineInput)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (hidden : Fin FieldMacToECMac.outputMacCount → HiddenRowSample)
    (activeLabels hiddenPads : EncPRF.PermutationIndex → Block)
    (curve : (index : EncPRF.PermutationIndex) → SharedCurveBranches index.1)
    (labels : EncPRF.PermutationIndex → Block)
    (goodRows : ¬ pointBranchCollision visible rows input targets hidden)
    (goodLabels : ¬ sharedCrossBranchCollision
      (pointSharedBranches visible rows input targets hidden activeLabels hiddenPads) curve labels)
    (index : EncPRF.PermutationIndex) (slot : Fin (pointSharedSlotCount index.1)) :
    let branches := pointSharedBranches visible rows input targets hidden activeLabels hiddenPads index
    Function.Injective (Sum.elim
      (fun row => (labels index ^^^ hiddenPads index) ^^^ branches.tweak row)
      (fun row => activeLabels index ^^^ branches.tweak row)) ∧
    Function.Injective (Sum.elim
      (fun row => branches.hiddenOffset slot row ^^^ (labels index ^^^ hiddenPads index))
      (fun row => branches.activeOffset slot row ^^^ activeLabels index)) := by
  dsimp only
  have good := (sharedCoordinateForbidden_good
    (pointSharedBranches visible rows input targets hidden activeLabels hiddenPads index)
    (curve index) (labels index) (fun member => goodLabels ⟨index, member⟩)).1
  have offsets := pointSharedBranches_offsets_injective visible rows input targets hidden
    activeLabels hiddenPads goodRows index slot
  exact ⟨sharedBranchDomain_injective _ _ _ _ _ pointSharedBranches_tweaks_injective good,
    sharedBranchRange_injective _ _ _ _ _ slot offsets.1 offsets.2 good⟩

end
end Kriterion.ArgoMAC.Security
