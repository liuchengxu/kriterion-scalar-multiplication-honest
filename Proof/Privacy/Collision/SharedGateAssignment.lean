import Proof.Privacy.Collision.SharedBranchCollision
import Proof.Privacy.Collision.SlotRatio

namespace Kriterion.ArgoMAC.Security
open Cryptography
open scoped ENNReal

noncomputable section
variable {Gate : Type*} [Fintype Gate] [Fintype Block]

/-- Each shared slot receives both label branches. Slot two receives the hash branch. -/
def sharedGateEvent (hashLabel padLabel : Block) (tweak : Gate → Block)
    (hashOffset : Fin 3 → Gate → Block) (padOffset : Fin 2 → Gate → Block)
    (slot : Fin 3) : Set (Equiv.Perm Block) :=
  {permutation | (∀ gate, permutation (hashLabel ^^^ tweak gate) =
      hashOffset slot gate ^^^ hashLabel) ∧
    ∀ shared : slot.val < 2, ∀ gate, permutation (padLabel ^^^ tweak gate) =
      padOffset ⟨slot.val, shared⟩ gate ^^^ padLabel}

/-- A shared slot fixes twice the number of gate assignments. -/
theorem sharedGateEvent_shared_mass (hashLabel padLabel : Block) (tweak : Gate → Block)
    (hashOffset : Fin 3 → Gate → Block) (padOffset : Fin 2 → Gate → Block)
    (tweaksDistinct : Function.Injective tweak)
    (hashDistinct : ∀ slot, Function.Injective (hashOffset slot))
    (padDistinct : ∀ slot, Function.Injective (padOffset slot))
    (retained : hashLabel ∉ sharedBranchForbidden padLabel tweak padOffset
      (fun slot => hashOffset slot.castSucc)) (slot : Fin 2) :
    (PMF.uniformOfFintype (Equiv.Perm Block)).toOuterMeasure
      (sharedGateEvent hashLabel padLabel tweak hashOffset padOffset slot.castSucc) =
      ((Fintype.card Block - 2 * Fintype.card Gate).factorial : ENNReal) /
        (Fintype.card Block).factorial := by
  have mass := indexedSumAssignment_mass
    (fun gate => hashLabel ^^^ tweak gate) (fun gate => hashOffset slot.castSucc gate ^^^ hashLabel)
    (fun gate => padLabel ^^^ tweak gate) (fun gate => padOffset slot gate ^^^ padLabel)
    (sharedBranchDomain_injective padLabel hashLabel tweak padOffset
      (fun s => hashOffset s.castSucc) tweaksDistinct retained)
    (sharedBranchRange_injective padLabel hashLabel tweak padOffset
      (fun s => hashOffset s.castSucc) slot (padDistinct slot)
      (hashDistinct slot.castSucc) retained)
  simpa only [sharedGateEvent, Fin.val_castSucc, slot.isLt, forall_const,
    Fin.eta, two_mul] using mass

/-- Slot two fixes only the hash assignments. -/
theorem sharedGateEvent_last_mass (hashLabel padLabel : Block) (tweak : Gate → Block)
    (hashOffset : Fin 3 → Gate → Block) (padOffset : Fin 2 → Gate → Block)
    (tweaksDistinct : Function.Injective tweak)
    (hashDistinct : Function.Injective (hashOffset 2)) :
    (PMF.uniformOfFintype (Equiv.Perm Block)).toOuterMeasure
      (sharedGateEvent hashLabel padLabel tweak hashOffset padOffset 2) =
      ((Fintype.card Block - Fintype.card Gate).factorial : ENNReal) /
        (Fintype.card Block).factorial := by
  simpa only [sharedGateEvent, show ¬ ((2 : Fin 3).val < 2) from by decide,
    forall_false, and_true] using indexedAssignment_mass
      (fun gate => hashLabel ^^^ tweak gate) (fun gate => hashOffset 2 gate ^^^ hashLabel)
      (slotInput_injective tweak tweaksDistinct hashLabel)
      (slotOutput_injective (hashOffset 2) hashDistinct hashLabel)

/-- Three independent permutations realize both branches with this exact mass. -/
theorem sharedGateAssignment_mass (hashLabel padLabel : Block) (tweak : Gate → Block)
    (hashOffset : Fin 3 → Gate → Block) (padOffset : Fin 2 → Gate → Block)
    (tweaksDistinct : Function.Injective tweak)
    (hashDistinct : ∀ slot, Function.Injective (hashOffset slot))
    (padDistinct : ∀ slot, Function.Injective (padOffset slot))
    (retained : hashLabel ∉ sharedBranchForbidden padLabel tweak padOffset
      (fun slot => hashOffset slot.castSucc)) :
    (PMF.uniformOfFintype (Fin 3 → Equiv.Perm Block)).toOuterMeasure
      {permutations | ∀ slot, permutations slot ∈
        sharedGateEvent hashLabel padLabel tweak hashOffset padOffset slot} =
      (((Fintype.card Block - 2 * Fintype.card Gate).factorial : ENNReal) /
        (Fintype.card Block).factorial) ^ 2 *
      (((Fintype.card Block - Fintype.card Gate).factorial : ENNReal) /
        (Fintype.card Block).factorial) := by
  rw [uniformFamily_event_product, Fin.prod_univ_three]
  have first := sharedGateEvent_shared_mass hashLabel padLabel tweak hashOffset padOffset
    tweaksDistinct hashDistinct padDistinct retained 0
  have second := sharedGateEvent_shared_mass hashLabel padLabel tweak hashOffset padOffset
    tweaksDistinct hashDistinct padDistinct retained 1
  rw [show (0 : Fin 2).castSucc = (0 : Fin 3) from rfl] at first
  rw [show (1 : Fin 2).castSucc = (1 : Fin 3) from rfl] at second
  rw [first, second, sharedGateEvent_last_mass _ _ _ _ _ tweaksDistinct (hashDistinct 2), pow_two]

end
end Kriterion.ArgoMAC.Security
