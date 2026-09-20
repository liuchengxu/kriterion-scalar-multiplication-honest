import Proof.Privacy.Collision.SharedPointAssignments
import Proof.Privacy.Collision.AdaptiveBadBound

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 2048

/-- This equivalence lists the actual shared curve slots for one input coordinate. -/
def curveFamilySlotEquiv (coordinate : EncPRF.Coordinate) :
    ({family : Fin 5 // curveSharedCoordinate family = coordinate} × Fin 2) ≃
      Fin (curveSharedSlotCount coordinate) :=
  (Fintype.equivFin _).trans (finCongr (curveSharedSlotCount_actual coordinate))

/-- The curve coordinate grouping matches the actual input-label wire. -/
theorem curveSharedCoordinate_wire (family : Fin 5) (position : Fin coordinateBitCount) :
    circuitGateWire (.inl (family, position)) = (curveSharedCoordinate family, position) := by
  fin_cases family <;> rfl

/-- Every curve family uses the single curve tweak, the digit count, as the paper does. -/
theorem curveSharedTweak (family : Fin 5) (position : Fin coordinateBitCount) :
    (rawCircuitLocation (.inl (family, position))).tweak = BitVec.ofNat 128 FieldMacToECMac.outputMacCount := by
  fin_cases family <;> rfl

/-- The grouped curve data retains the actual raw source offsets. -/
def curveSharedBranches (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (input : AffineInput) (activeLabels : EncPRF.PermutationIndex → Block)
    (index : EncPRF.PermutationIndex) : SharedCurveBranches index.1 := {
  activeLabel := activeLabels index
  tweak := fun _ => BitVec.ofNat 128 FieldMacToECMac.outputMacCount
  activeOffset := fun slot _ =>
    let use := (curveFamilySlotEquiv index.1).symm slot
    circuitSourceOffset source lifts (.inl (use.1.1, index.2))
      (sharedBranchRole (inputSelectedLabelBit input index) use.2) ^^^ BitVec.ofNat 128 FieldMacToECMac.outputMacCount
  hiddenOffset := fun slot _ =>
    let use := (curveFamilySlotEquiv index.1).symm slot
    circuitSourceOffset source lifts (.inl (use.1.1, index.2))
      (sharedBranchRole (!(inputSelectedLabelBit input index)) use.2) ^^^ BitVec.ofNat 128 FieldMacToECMac.outputMacCount
}

/-- The grouped active offset equals its actual curve gate offset. -/
theorem curveSharedBranches_activeOffset (source : CircuitMaskSample)
    (lifts : RawCircuitGate → FullHashLift) (input : AffineInput)
    (activeLabels : EncPRF.PermutationIndex → Block)
    (family : Fin 5) (position : Fin coordinateBitCount) (slot : Fin 2) (row : Fin 1) :
    (curveSharedBranches source lifts input activeLabels (curveSharedCoordinate family, position)).activeOffset
      (curveFamilySlotEquiv (curveSharedCoordinate family) (⟨family, rfl⟩, slot)) row =
      circuitSourceOffset source lifts (.inl (family, position))
        (sharedBranchRole (inputSelectedLabelBit input (circuitGateWire (.inl (family, position)))) slot) ^^^
          (rawCircuitLocation (.inl (family, position))).tweak := by
  simp only [curveSharedBranches, Equiv.symm_apply_apply, curveSharedCoordinate_wire, curveSharedTweak]

/-- The grouped hidden offset equals its actual curve gate offset. -/
theorem curveSharedBranches_hiddenOffset (source : CircuitMaskSample)
    (lifts : RawCircuitGate → FullHashLift) (input : AffineInput)
    (activeLabels : EncPRF.PermutationIndex → Block)
    (family : Fin 5) (position : Fin coordinateBitCount) (slot : Fin 2) (row : Fin 1) :
    (curveSharedBranches source lifts input activeLabels (curveSharedCoordinate family, position)).hiddenOffset
      (curveFamilySlotEquiv (curveSharedCoordinate family) (⟨family, rfl⟩, slot)) row =
      circuitSourceOffset source lifts (.inl (family, position))
        (sharedBranchRole (!(inputSelectedLabelBit input (circuitGateWire (.inl (family, position))))) slot) ^^^
          (rawCircuitLocation (.inl (family, position))).tweak := by
  simp only [curveSharedBranches, Equiv.symm_apply_apply, curveSharedCoordinate_wire, curveSharedTweak]

/-- A retained coordinate label separates both actual curve branches in each shared slot. -/
theorem curveSharedBranches_assignments_injective (source : CircuitMaskSample)
    (lifts : RawCircuitGate → FullHashLift) (input : AffineInput)
    (activeLabels : EncPRF.PermutationIndex → Block)
    (point : (index : EncPRF.PermutationIndex) → SharedPointBranches index.1)
    (labels : EncPRF.PermutationIndex → Block)
    (goodLabels : ¬ sharedCrossBranchCollision point (curveSharedBranches source lifts input activeLabels) labels)
    (index : EncPRF.PermutationIndex) (slot : Fin (curveSharedSlotCount index.1)) :
    let branches := curveSharedBranches source lifts input activeLabels index
    Function.Injective (Sum.elim
      (fun row => labels index ^^^ branches.tweak row)
      (fun row => activeLabels index ^^^ branches.tweak row)) ∧
    Function.Injective (Sum.elim
      (fun row => branches.hiddenOffset slot row ^^^ labels index)
      (fun row => branches.activeOffset slot row ^^^ activeLabels index)) := by
  dsimp only
  have good := (sharedCoordinateForbidden_good (point index)
    (curveSharedBranches source lifts input activeLabels index) (labels index)
    (fun member => goodLabels ⟨index, member⟩)).2
  have injective (function : Fin 1 → Block) : Function.Injective function :=
    fun _ _ _ => Subsingleton.elim _ _
  exact ⟨sharedBranchDomain_injective _ _ _ _ _ (injective _) good,
    sharedBranchRange_injective _ _ _ _ _ slot (injective _) (injective _) good⟩

end
end Kriterion.ArgoMAC.Security
