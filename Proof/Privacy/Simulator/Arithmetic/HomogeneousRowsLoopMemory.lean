import Proof.Privacy.Simulator.Arithmetic.HomogeneousRowsBlock
import Proof.Privacy.Simulator.Arithmetic.DrawMemoryPreserve

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The point load preserves every caller register. -/
theorem homogeneousRowLoaded_caller (base : Memory) (index : Nat) (register : Register) (caller : 9 ≤ register.val) :
    (homogeneousRowLoaded base index).registers register = base.registers register := by
  have different (target : Register) (small : target.val < 9) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [homogeneousRowLoaded, Function.update_of_ne (different 4 (by decide)),
    Function.update_of_ne (different 3 (by decide)), Function.update_of_ne (different 2 (by decide)),
    Function.update_of_ne (different 8 (by decide))]

/-- Each row loads a free point except the first row. -/
def homogeneousRowInput (base : Memory) (index : Nat) : Memory :=
  if index = 0 then base else homogeneousRowLoaded base index

/-- Every row input preserves caller registers and all stored data. -/
theorem homogeneousRowInput_caller (base : Memory) (index : Nat) (register : Register) (caller : 9 ≤ register.val) :
    (homogeneousRowInput base index).registers register = base.registers register := by
  unfold homogeneousRowInput
  split
  · rfl
  · exact homogeneousRowLoaded_caller base index register caller

/-- Every row input preserves RAM. -/
theorem homogeneousRowInput_ram (base : Memory) (index : Nat) : (homogeneousRowInput base index).ram = base.ram := by
  unfold homogeneousRowInput; split <;> rfl

/-- Every row input preserves the bit stacks. -/
theorem homogeneousRowInput_bits (base : Memory) (index : Nat) : (homogeneousRowInput base index).bits = base.bits := by
  unfold homogeneousRowInput; split <;> rfl

/-- The row-prefix memory records the exact sequential target writes. -/
def homogeneousRowsPrefixMemory [BN254.FieldCertificate] (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase) :
    Nat → Memory → Memory
  | 0, base => base
  | n + 1, base => homogeneousRowStored (homogeneousRowInput (homogeneousRowsPrefixMemory points scales n base) n)
      n (points n) (scales n)

/-- The row-prefix source consists of its homogeneous coordinate triples. -/
def homogeneousRowsWords [BN254.FieldCertificate] (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase)
    (count : Nat) : List Word :=
  (List.range count).flatMap fun index => homogeneousWords (Security.homogeneousOfPoint (points index) (scales index))

/-- Each row adds exactly three source words. -/
theorem homogeneousRowsWords_succ [BN254.FieldCertificate] (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase)
    (count : Nat) : homogeneousRowsWords points scales (count + 1) = homogeneousRowsWords points scales count ++
      homogeneousWords (Security.homogeneousOfPoint (points count) (scales count)) := by
  simp [homogeneousRowsWords, List.range_succ]

/-- The homogeneous source has three words per row. -/
theorem homogeneousRowsWords_length [BN254.FieldCertificate] (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase)
    (count : Nat) : (homogeneousRowsWords points scales count).length = 3 * count := by
  induction count with
  | zero => rfl
  | succ count ih => rw [homogeneousRowsWords_succ, List.length_append, ih]; simp [homogeneousWords]; omega

/-- Every row prefix preserves caller registers. -/
theorem homogeneousRowsPrefixMemory_caller [BN254.FieldCertificate]
    (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase) (count : Nat) (base : Memory)
    (register : Register) (caller : 9 ≤ register.val) :
    (homogeneousRowsPrefixMemory points scales count base).registers register = base.registers register := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [homogeneousRowsPrefixMemory, homogeneousRowStored_caller _ _ _ _ register caller,
        homogeneousRowInput_caller _ _ register caller, ih]

/-- Every row prefix preserves the bit stacks. -/
theorem homogeneousRowsPrefixMemory_bits [BN254.FieldCertificate]
    (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase) (count : Nat) (base : Memory) :
    (homogeneousRowsPrefixMemory points scales count base).bits = base.bits := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (homogeneousRowInput (homogeneousRowsPrefixMemory points scales count base) count).bits = base.bits
      rw [homogeneousRowInput_bits, ih]

/-- Every row prefix has the exact sequential source RAM law. -/
theorem homogeneousRowsPrefixMemory_ram [BN254.FieldCertificate]
    (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase) (count : Nat) (base : Memory) :
    (homogeneousRowsPrefixMemory points scales count base).ram =
      storeDrawWords (base.registers 13) 0 base.ram (homogeneousRowsWords points scales count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [homogeneousRowsPrefixMemory, homogeneousRowStored,
        homogeneousRowInput_caller _ _ 13 (by decide), homogeneousRowsPrefixMemory_caller _ _ _ _ 13 (by decide),
        homogeneousRowInput_ram, ih]
      rw [homogeneousRowsWords_succ, storeDrawWords_append, homogeneousRowsWords_length, Nat.zero_add]

end Kriterion.ArgoMAC.ArithmeticSimulator
