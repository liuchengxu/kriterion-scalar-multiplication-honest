import Proof.Privacy.Simulator.Arithmetic.SelectedLabelStoreMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The store sequence preserves every caller pointer. -/
theorem selectedLabelStores_caller (indices : List (Fin 508)) (memory : Memory)
    (register : Register) (caller : 11 ≤ register.val) :
    (executeLinear (selectedLabelStores indices) memory).registers register = memory.registers register := by
  induction indices generalizing memory with
  | nil => rfl
  | cons index rest ih =>
      simp only [selectedLabelStores, List.flatMap_cons, executeLinear_append]
      change (executeLinear (selectedLabelStores rest) (executeLinear (selectedLabelStore index) memory)).registers register = _
      rw [ih, selectedLabelStore_caller index memory register caller]

/-- The store sequence preserves every cell outside its destination addresses. -/
theorem selectedLabelStores_outside (indices : List (Fin 508)) (memory : Memory) (address : Word)
    (outside : ∀ index ∈ indices, address ≠ memory.registers 14 + BitVec.ofNat 256 index.val) :
    (executeLinear (selectedLabelStores indices) memory).ram address = memory.ram address := by
  induction indices generalizing memory with
  | nil => rfl
  | cons index rest ih =>
      simp only [selectedLabelStores, List.flatMap_cons, executeLinear_append]
      change (executeLinear (selectedLabelStores rest) (executeLinear (selectedLabelStore index) memory)).ram address = _
      rw [ih]
      · rw [selectedLabelStore_ram, Function.update_of_ne (outside index (List.mem_cons_self))]
      · intro selected member
        rw [selectedLabelStore_caller index memory 14 (by decide)]
        exact outside selected (List.mem_cons_of_mem index member)

attribute [local irreducible] selectedLabelStores selectedLabelStoreProgram

/-- The complete original-label store preserves every cell outside its fixed destination. -/
theorem selectedLabelStoreCode_outside (memory : Memory) (address : Word)
    (outside : ∀ index : Fin 508, address ≠ memory.registers 14 + BitVec.ofNat 256 index.val) :
    (executeLinear selectedLabelStoreCode memory).ram address = memory.ram address := by
  rw [selectedLabelStoreCode_eq, selectedLabelStoreProgram]
  exact selectedLabelStores_outside (List.finRange 508) memory address (fun index _ => outside index)

/-- The complete original-label store preserves every caller pointer. -/
theorem selectedLabelStoreCode_caller (memory : Memory) (register : Register) (caller : 11 ≤ register.val) :
    (executeLinear selectedLabelStoreCode memory).registers register = memory.registers register := by
  rw [selectedLabelStoreCode_eq, selectedLabelStoreProgram]
  exact selectedLabelStores_caller (List.finRange 508) memory register caller

end Kriterion.ArgoMAC.ArithmeticSimulator
