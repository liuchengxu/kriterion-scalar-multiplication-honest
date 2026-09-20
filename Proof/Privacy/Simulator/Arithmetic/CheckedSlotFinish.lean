import Proof.Privacy.Simulator.Arithmetic.CheckedSlotHostCode
import Proof.Privacy.Simulator.Arithmetic.CheckedSlotMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The successful tail installs the override and appends its requested history pair. -/
theorem checkedSlotBlock_finish [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 305 → Fin (host.size + 1)) (present : ContainsCheckedSlot host attempts labels)
    (memory : Memory) (fuel : Nat) :
    run host (40 + fuel) ⟨labels 260, memory⟩ =
      (run host fuel ⟨labels 300, checkedSlotFinished memory⟩).map
        (Option.map fun result => (result.1, result.2 + 40)) := by
  have target := linear_continue host checkedSlotTarget (labels ∘ checkedSlotTargetLabels)
    (checkedSlotBlock_target host attempts labels present) memory (17 + (4 + (15 + fuel)))
  have overlay := overlayAppend_continue host (labels ∘ checkedSlotOverlayLabels)
    (checkedSlotBlock_overlay host attempts labels present) (executeLinear checkedSlotTarget memory) (4 + (15 + fuel))
  have history := linear_continue host checkedSlotHistory (labels ∘ checkedSlotHistoryLabels)
    (checkedSlotBlock_history host attempts labels present)
    (overlayAppended (executeLinear checkedSlotTarget memory)) (15 + fuel)
  have append := historyAppend_continue host (labels ∘ checkedSlotAppendLabels)
    (checkedSlotBlock_append host attempts labels present)
    (executeLinear checkedSlotHistory (overlayAppended (executeLinear checkedSlotTarget memory))) fuel
  simp only [show checkedSlotTarget.length = 4 from rfl] at target
  simp only [show checkedSlotHistory.length = 4 from rfl] at history
  change run host (4 + (17 + (4 + (15 + fuel)))) ⟨labels 260, memory⟩ = _ at target
  change run host (17 + (4 + (15 + fuel))) ⟨labels 264, executeLinear checkedSlotTarget memory⟩ = _ at overlay
  change run host (4 + (15 + fuel)) ⟨labels 281, overlayAppended (executeLinear checkedSlotTarget memory)⟩ = _ at history
  change run host (15 + fuel) ⟨labels 285, executeLinear checkedSlotHistory (overlayAppended (executeLinear checkedSlotTarget memory))⟩ = _ at append
  rw [show 40 + fuel = 4 + (17 + (4 + (15 + fuel))) by omega, target]
  change (run host _ ⟨labels 264, executeLinear checkedSlotTarget memory⟩).map _ = _
  rw [overlay]
  change ((run host _ ⟨labels 281, overlayAppended (executeLinear checkedSlotTarget memory)⟩).map _).map _ = _
  rw [history]
  change (((run host _ ⟨labels 285, executeLinear checkedSlotHistory (overlayAppended (executeLinear checkedSlotTarget memory))⟩).map _).map _).map _ = _
  rw [append]
  change ((((run host fuel ⟨labels 300, checkedSlotFinished memory⟩).map _).map _).map _).map _ = _
  simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The collision tail records bad without a private oracle call. -/
theorem checkedSlotBlock_collision_return [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 305 → Fin (host.size + 1)) (present : ContainsCheckedSlot host attempts labels)
    (memory : Memory) (fuel : Nat) :
    run host (3 + fuel) ⟨labels 301, memory⟩ =
      (run host fuel ⟨labels 300, executeLinear checkedSlotCollision memory⟩).map
        (Option.map fun result => (result.1, result.2 + 3)) := by
  exact linear_continue host checkedSlotCollision (labels ∘ checkedSlotCollisionLabels)
    (checkedSlotBlock_collision host attempts labels present) memory fuel

end Kriterion.ArgoMAC.ArithmeticSimulator
