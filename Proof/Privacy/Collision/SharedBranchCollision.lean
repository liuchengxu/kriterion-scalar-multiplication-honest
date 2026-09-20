import Proof.Privacy.Collision.SlotCounting

namespace Kriterion.ArgoMAC.Security
open Cryptography
open scoped ENNReal

noncomputable section

variable {Gate Slot : Type*} [Fintype Gate] [Fintype Slot]

/-- All slots use the same label pair and digit tweaks.
The domain exclusion therefore occurs once across the slots. -/
def sharedBranchForbidden (activeLabel : Block) (tweak : Gate → Block)
    (activeOffset hiddenOffset : Slot → Gate → Block) : Finset Block :=
  Finset.univ.image (fun pair : Gate × Gate =>
    activeLabel ^^^ tweak pair.2 ^^^ tweak pair.1) ∪
  Finset.univ.image (fun use : Slot × Gate × Gate =>
    activeOffset use.1 use.2.2 ^^^ activeLabel ^^^ hiddenOffset use.1 use.2.1)

/-- Each gate pair excludes one domain value and one range value per slot. -/
theorem sharedBranchForbidden_card_le (activeLabel : Block) (tweak : Gate → Block)
    (activeOffset hiddenOffset : Slot → Gate → Block) :
    (sharedBranchForbidden activeLabel tweak activeOffset hiddenOffset).card ≤
      (Fintype.card Slot + 1) * Fintype.card Gate ^ 2 := by
  classical
  unfold sharedBranchForbidden
  apply (Finset.card_union_le _ _).trans
  apply (Nat.add_le_add Finset.card_image_le Finset.card_image_le).trans
  simp only [Finset.card_univ, Fintype.card_prod]
  nlinarith

/-- A retained hidden label cannot share an input with the active branch. -/
theorem sharedBranchDomain_ne (activeLabel hiddenLabel : Block) (tweak : Gate → Block)
    (activeOffset hiddenOffset : Slot → Gate → Block)
    (retained : hiddenLabel ∉ sharedBranchForbidden activeLabel tweak activeOffset hiddenOffset)
    (hiddenGate activeGate : Gate) :
    hiddenLabel ^^^ tweak hiddenGate ≠ activeLabel ^^^ tweak activeGate := by
  intro equal
  apply retained
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨(hiddenGate, activeGate), Finset.mem_univ _, ?_⟩
  rw [← equal, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- A retained hidden label cannot share an output with the active branch. -/
theorem sharedBranchRange_ne (activeLabel hiddenLabel : Block) (tweak : Gate → Block)
    (activeOffset hiddenOffset : Slot → Gate → Block)
    (retained : hiddenLabel ∉ sharedBranchForbidden activeLabel tweak activeOffset hiddenOffset)
    (slot : Slot) (hiddenGate activeGate : Gate) :
    hiddenOffset slot hiddenGate ^^^ hiddenLabel ≠ activeOffset slot activeGate ^^^ activeLabel := by
  intro equal
  apply retained
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨(slot, hiddenGate, activeGate), Finset.mem_univ _, ?_⟩
  rw [← equal, BitVec.xor_comm (hiddenOffset slot hiddenGate) hiddenLabel,
    BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- A uniform hidden label pays the domain exclusion only once. -/
theorem sharedBranchForbidden_mass_le [Fintype Block]
    (activeLabel : Block) (tweak : Gate → Block)
    (activeOffset hiddenOffset : Slot → Gate → Block) :
    (PMF.uniformOfFintype Block).toOuterMeasure
      {hiddenLabel | hiddenLabel ∈ sharedBranchForbidden activeLabel tweak activeOffset hiddenOffset} ≤
        (((Fintype.card Slot + 1) * Fintype.card Gate ^ 2 : Nat) : ENNReal) /
          Fintype.card Block := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  apply ENNReal.div_le_div_right
  exact_mod_cast (Fintype.card_of_subtype _ (fun _ => Iff.rfl)).trans_le
    (sharedBranchForbidden_card_le activeLabel tweak activeOffset hiddenOffset)

/-- The active and hidden domains form one injective permutation assignment. -/
theorem sharedBranchDomain_injective (activeLabel hiddenLabel : Block) (tweak : Gate → Block)
    (activeOffset hiddenOffset : Slot → Gate → Block)
    (distinct : Function.Injective tweak)
    (retained : hiddenLabel ∉ sharedBranchForbidden activeLabel tweak activeOffset hiddenOffset) :
    Function.Injective (Sum.elim (fun gate => hiddenLabel ^^^ tweak gate)
      (fun gate => activeLabel ^^^ tweak gate)) :=
  Sum.elim_injective.mpr ⟨slotInput_injective tweak distinct hiddenLabel,
    slotInput_injective tweak distinct activeLabel,
    sharedBranchDomain_ne activeLabel hiddenLabel tweak activeOffset hiddenOffset retained⟩

/-- The active and hidden ranges form one injective permutation assignment. -/
theorem sharedBranchRange_injective (activeLabel hiddenLabel : Block) (tweak : Gate → Block)
    (activeOffset hiddenOffset : Slot → Gate → Block) (slot : Slot)
    (activeDistinct : Function.Injective (activeOffset slot))
    (hiddenDistinct : Function.Injective (hiddenOffset slot))
    (retained : hiddenLabel ∉ sharedBranchForbidden activeLabel tweak activeOffset hiddenOffset) :
    Function.Injective (Sum.elim (fun gate => hiddenOffset slot gate ^^^ hiddenLabel)
      (fun gate => activeOffset slot gate ^^^ activeLabel)) :=
  Sum.elim_injective.mpr ⟨slotOutput_injective _ hiddenDistinct hiddenLabel,
    slotOutput_injective _ activeDistinct activeLabel,
    sharedBranchRange_ne activeLabel hiddenLabel tweak activeOffset hiddenOffset retained slot⟩

end
end Kriterion.ArgoMAC.Security
