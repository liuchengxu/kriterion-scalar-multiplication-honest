import Construction.Simulator.GateDirectiveScratch
import Proof.Privacy.Simulator.Arithmetic.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The save block stores the prepared input, ranges, count, and caller pointers. -/
theorem gateDirectiveSave_values (base : Memory) :
    let result := executeLinear gateDirectiveSave base
    result.ram 16 = base.registers 9 ∧ result.ram 17 = base.registers 4 ∧
    result.ram 18 = base.registers 5 ∧ result.ram 19 = base.registers 6 ∧
    result.ram 20 = base.registers 7 ∧ result.ram 21 = base.registers 11 ∧
    result.ram 22 = base.registers 12 ∧ result.ram 23 = base.registers 13 ∧
    result.ram 24 = base.registers 14 ∧ result.ram 25 = base.registers 15 := by
  simp [gateDirectiveSave, executeLinear, LinearInstruction.execute]

/-- The save block preserves every cell outside its ten scratch cells. -/
theorem gateDirectiveSave_outside (base : Memory) (address : Word)
    (outside : address ≠ 16 ∧ address ≠ 17 ∧ address ≠ 18 ∧ address ≠ 19 ∧ address ≠ 20 ∧
      address ≠ 21 ∧ address ≠ 22 ∧ address ≠ 23 ∧ address ≠ 24 ∧ address ≠ 25) :
    (executeLinear gateDirectiveSave base).ram address = base.ram address := by
  rcases outside with ⟨h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  simp only [gateDirectiveSave, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_apply, Fin.reduceEq, ↓reduceIte]
  simp only [BitVec.ofNat_eq_ofNat] at *
  simp [h16,h17,h18,h19,h20,h21,h22,h23,h24,h25]

/-- The save block preserves every bit stack. -/
theorem gateDirectiveSave_bits (base : Memory) :
    (executeLinear gateDirectiveSave base).bits = base.bits := by
  simp [gateDirectiveSave, executeLinear, LinearInstruction.execute]

/-- The restore block reads the five saved caller pointers. -/
theorem gateDirectiveRestore_values (base : Memory) :
    let result := executeLinear gateDirectiveRestore base
    result.registers 11 = base.ram 21 ∧ result.registers 12 = base.ram 22 ∧
    result.registers 13 = base.ram 23 ∧ result.registers 14 = base.ram 24 ∧
    result.registers 15 = base.ram 25 := by
  simp [gateDirectiveRestore, executeLinear, LinearInstruction.execute]

/-- The restore block preserves RAM and all bit stacks. -/
theorem gateDirectiveRestore_data (base : Memory) :
    (executeLinear gateDirectiveRestore base).ram = base.ram ∧
    (executeLinear gateDirectiveRestore base).bits = base.bits := ⟨rfl, rfl⟩

/-- The slot loader returns the exact oracle input and saves the exact target. -/
theorem gateSlotLoad_values (oracleIndex : Nat) (slot : Fin 3) (base : Memory) :
    let result := executeLinear (gateSlotLoad oracleIndex slot) base
    result.registers 8 = base.ram 16 ∧ result.registers 9 = BitVec.ofNat 256 oracleIndex ∧
    result.registers 10 = 0 ∧
    result.ram = Function.update base.ram 14 (base.ram (BitVec.ofNat 256 (17 + slot.val))) ∧
    result.bits = base.bits := by
  simp [gateSlotLoad, executeLinear, LinearInstruction.execute]

/-- The slot loader preserves each caller register from eleven through fifteen. -/
theorem gateSlotLoad_caller (oracleIndex : Nat) (slot : Fin 3) (base : Memory)
    (register : Register) (caller : 11 ≤ register.val) :
    (executeLinear (gateSlotLoad oracleIndex slot) base).registers register = base.registers register := by
  have different (target : Register) (small : target.val < 11) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [gateSlotLoad, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne (different 0 (by decide)), Function.update_of_ne (different 1 (by decide)),
    Function.update_of_ne (different 8 (by decide)), Function.update_of_ne (different 9 (by decide)),
    Function.update_of_ne (different 10 (by decide))]

/-- The save, restore, and slot loader blocks charge their exact fixed instruction counts. -/
theorem gateDirectiveScratch_lengths : gateDirectiveSave.length = 20 ∧ gateDirectiveRestore.length = 10 ∧
    ∀ oracleIndex slot, (gateSlotLoad oracleIndex slot).length = 8 := by
  exact ⟨rfl, rfl, fun _ _ => rfl⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
