import Proof.Privacy.Simulator.Arithmetic.RetargetFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] retargetAt

/-- Every complete row preserves the four factors and all caller pointers. -/
theorem retargetPointRow_preserves (row : Fin FieldMacToECMac.outputMacCount) (memory : Memory) :
    (executeLinear (retargetPointRow row) memory).bits = memory.bits ∧
    ∀ register : Register, 5 ≤ register.val → register ≠ 10 → register ≠ 13 →
      (executeLinear (retargetPointRow row) memory).registers register = memory.registers register := by
  simp only [retargetPointRow, executeLinear_append]
  have save (kind : RetargetKind) (source target : Nat) (base : Memory) :=
    retargetAt_preserves kind source 14 target base (by decide) (by decide)
  constructor
  · rw [(save .z _ _ _).1, (save .y _ _ _).1, (save .x _ _ _).1]
  · intro register lower first second
    rw [(save .z _ _ _).2 register lower first second,
      (save .y _ _ _).2 register lower first second,
      (save .x _ _ _).2 register lower first second]

/-- Each row writes only its three selected low-target cells. -/
def OutsidePointRow (pointer : Word) (row : Fin FieldMacToECMac.outputMacCount) (address : Word) : Prop :=
  address ≠ pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 6105) + 762 ∧
  address ≠ pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 3815) + 508 ∧
  address ≠ pointer + BitVec.ofNat 256 (1017 + 9158 * row.val) + 1016

/-- A complete row preserves every other RAM word. -/
theorem retargetPointRow_outside (row : Fin FieldMacToECMac.outputMacCount) (memory : Memory) (address : Word)
    (outside : OutsidePointRow (memory.registers 11) row address) :
    (executeLinear (retargetPointRow row) memory).ram address = memory.ram address := by
  simp only [retargetPointRow, executeLinear_append]
  have pointer (kind : RetargetKind) (source target : Nat) (base : Memory) :=
    (retargetAt_preserves kind source 14 target base (by decide) (by decide)).2 11 (by decide) (by decide) (by decide)
  rw [retargetAt_outside .z _ 14 _ _ (by decide) (by decide) address]
  · rw [retargetAt_outside .y _ 14 _ _ (by decide) (by decide) address]
    · exact retargetAt_outside .x _ 14 _ memory (by decide) (by decide) address outside.1
    · rw [pointer .x]
      exact outside.2.1
  · rw [pointer .y, pointer .x]
    exact outside.2.2

/-- Any consecutive row list preserves the factors and caller pointers. -/
theorem retargetPointRows_preserves (rows : List (Fin FieldMacToECMac.outputMacCount)) (memory : Memory) :
    (executeLinear (rows.flatMap retargetPointRow) memory).bits = memory.bits ∧
    ∀ register : Register, 5 ≤ register.val → register ≠ 10 → register ≠ 13 →
      (executeLinear (rows.flatMap retargetPointRow) memory).registers register = memory.registers register := by
  induction rows generalizing memory with
  | nil => exact ⟨rfl, fun _ _ _ _ => rfl⟩
  | cons row rest ih =>
      simp only [List.flatMap_cons, executeLinear_append]
      have saved := retargetPointRow_preserves row memory
      have later := ih (executeLinear (retargetPointRow row) memory)
      exact ⟨later.1.trans saved.1, fun register lower first second =>
        (later.2 register lower first second).trans (saved.2 register lower first second)⟩

/-- A row list preserves every word outside all its low-target updates. -/
theorem retargetPointRows_outside (rows : List (Fin FieldMacToECMac.outputMacCount)) (memory : Memory) (address : Word)
    (outside : ∀ row ∈ rows, OutsidePointRow (memory.registers 11) row address) :
    (executeLinear (rows.flatMap retargetPointRow) memory).ram address = memory.ram address := by
  induction rows generalizing memory with
  | nil => rfl
  | cons row rest ih =>
      simp only [List.flatMap_cons, executeLinear_append]
      rw [ih]
      · exact retargetPointRow_outside row memory address (outside row (List.mem_cons_self))
      · intro later member
        rw [(retargetPointRow_preserves row memory).2 11 (by decide) (by decide) (by decide)]
        exact outside later (List.mem_cons_of_mem row member)

/-- The complete point code retains its symbolic row list. -/
theorem retargetPointCode_rows : retargetPointCode =
    retargetInput ++ (List.finRange FieldMacToECMac.outputMacCount).flatMap retargetPointRow := by
  rw [retargetPointCode_eq, retargetPointProgram, List.ofFn_eq_map, ← List.flatMap_def]

/-- The complete point pass preserves caller stacks and caller pointers. -/
theorem retargetPointCode_preserves (memory : Memory) :
    (executeLinear retargetPointCode memory).bits = memory.bits ∧
    ∀ register : Register, 9 ≤ register.val → register ≠ 10 → register ≠ 13 →
      (executeLinear retargetPointCode memory).registers register = memory.registers register := by
  rw [retargetPointCode_rows, executeLinear_append]
  have initial := retargetInput_preserves memory
  have rows := retargetPointRows_preserves (List.finRange FieldMacToECMac.outputMacCount) (executeLinear retargetInput memory)
  exact ⟨rows.1.trans initial.2.1, fun register lower first second =>
    (rows.2 register (by omega) first second).trans (initial.2.2 register lower)⟩

/-- The complete point pass preserves every word outside its 273 low targets. -/
theorem retargetPointCode_outside (memory : Memory) (address : Word)
    (outside : ∀ row : Fin FieldMacToECMac.outputMacCount, OutsidePointRow (memory.registers 11) row address) :
    (executeLinear retargetPointCode memory).ram address = memory.ram address := by
  rw [retargetPointCode_rows, executeLinear_append, retargetPointRows_outside]
  · exact congrFun (retargetInput_preserves memory).1 address
  · intro row member
    rw [(retargetInput_preserves memory).2.2 11 (by decide)]
    exact outside row

end Kriterion.ArgoMAC.ArithmeticSimulator
