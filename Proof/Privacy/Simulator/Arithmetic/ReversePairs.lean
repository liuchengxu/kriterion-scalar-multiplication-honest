import Proof.Privacy.Simulator.Arithmetic.SwapTable
import Proof.Privacy.Simulator.Arithmetic.ReverseSwapTable
import Mathlib.Data.List.Induction

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A concatenated pair list occupies two consecutive RAM regions. -/
theorem RepresentsPairs.append (first second : List (Word × Word))
    (ram : Word → Word) (address : Word) :
    RepresentsPairs ram address (first ++ second) ↔
      RepresentsPairs ram address first ∧
      RepresentsPairs ram (address + BitVec.ofNat 256 (2 * first.length)) second := by
  induction first generalizing address with
  | nil => simp [RepresentsPairs]
  | cons pair rest ih =>
      simp only [List.cons_append, RepresentsPairs, List.length_cons]
      rw [ih]
      have advance : address + 2#256 + BitVec.ofNat 256 (2 * rest.length) =
          address + BitVec.ofNat 256 (2 * (rest.length + 1)) := by
        simp [Nat.mul_add, BitVec.ofNat_add, add_assoc, add_comm, add_left_comm]
      rw [advance]
      tauto

/-- The same RAM region represents the reversed pair list when the pointer moves backward. -/
theorem RepresentsPairs.reverse (pairs : List (Word × Word)) (ram : Word → Word)
    (address : Word) (represented : RepresentsPairs ram address pairs) :
    RepresentsReversePairs ram (address + BitVec.ofNat 256 (2 * pairs.length) - 2#256)
      pairs.reverse := by
  induction pairs using List.reverseRecOn with
  | nil => trivial
  | @append_singleton rest pair ih =>
      obtain ⟨before, last⟩ := (RepresentsPairs.append rest [pair] ram address).mp represented
      have finish : address + BitVec.ofNat 256 (2 * (rest ++ [pair]).length) - 2#256 =
          address + BitVec.ofNat 256 (2 * rest.length) := by
        simp only [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
        abel
      rw [List.reverse_append, List.reverse_singleton, List.singleton_append, finish]
      rcases last with ⟨left, right, _⟩
      exact ⟨left, right, ih before⟩

/-- Reversing the transpositions gives the inverse sparse permutation. -/
theorem swaps_reverse (pairs : List (Word × Word)) :
    Security.OperationalOracle.swaps pairs.reverse = (Security.OperationalOracle.swaps pairs).symm := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      rw [List.reverse_cons, Security.OperationalOracle.swaps_append, ih]
      apply Equiv.ext
      intro value
      simp [Security.OperationalOracle.swaps]

/-- Reverse traversal computes the inverse permutation from the original RAM layout. -/
theorem applyReverseTableSwaps_inverse (pairs : List (Word × Word)) (ram : Word → Word)
    (address value : Word) (represented : RepresentsPairs ram address pairs) :
    applyReverseTableSwaps pairs.length ram
      (address + BitVec.ofNat 256 (2 * pairs.length) - 2#256) value =
      (Security.OperationalOracle.swaps pairs).symm value := by
  have source := applyReverseTableSwaps_source pairs.reverse ram
    (address + BitVec.ofNat 256 (2 * pairs.length) - 2#256) value
    (RepresentsPairs.reverse pairs ram address represented)
  simpa only [List.length_reverse, swaps_reverse] using source

/-- The reverse machine returns the inverse sparse permutation from the same RAM table. -/
theorem reverseSwapTable_source [BN254.FieldCertificate]
    (pairs : List (Word × Word)) (memory : Memory) (address : Word)
    (fits : pairs.length < 2 ^ 256)
    (counter : memory.registers 10 = BitVec.ofNat 256 pairs.length)
    (cursor : memory.registers 9 = address + BitVec.ofNat 256 (2 * pairs.length) - 2#256)
    (represented : RepresentsPairs memory.ram address pairs) :
    (run reverseSwapTable ((reverseSwapScan pairs.length (reverseSwapInitial memory)).2 + 2)
      ⟨0, memory⟩).map (Option.map fun result => result.1.memory.registers 8) =
      PMF.pure (some ((Security.OperationalOracle.swaps pairs).symm (memory.registers 8))) := by
  rw [reverseSwapTable_run pairs.length memory fits counter, PMF.pure_map]
  simp only [Option.map_some, reverseSwapScan_source]
  simp only [reverseSwapInitial,
    Function.update_of_ne (by decide : (8 : Register) ≠ 14),
    Function.update_of_ne (by decide : (8 : Register) ≠ 15),
    Function.update_of_ne (by decide : (9 : Register) ≠ 14),
    Function.update_of_ne (by decide : (9 : Register) ≠ 15)]
  rw [cursor, applyReverseTableSwaps_inverse pairs memory.ram address (memory.registers 8) represented]

end Kriterion.ArgoMAC.ArithmeticSimulator
