import Proof.Privacy.Simulator.Arithmetic.HomogeneousRowsLoopMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The destination does not overlap either input region.
The destination holds `3 * rows` words: one accumulator row plus the `rows - 1`
free points register ten addresses, so the free-point region is only
`3 * (rows - 1)` words wide. Register eleven addresses the scales, which are
also read `3 * (rows - 1)` deep at most. -/
def HomogeneousRegionsDisjoint (base : Memory) (rows : Nat) : Prop :=
  ∀ i, i < 3 * (rows - 1) → ∀ j, j < 3 * rows →
    base.registers 10 + BitVec.ofNat 256 i ≠ base.registers 13 + BitVec.ofNat 256 j ∧
    base.registers 11 + BitVec.ofNat 256 i ≠ base.registers 13 + BitVec.ofNat 256 j

/-- Every row prefix preserves both input regions. -/
theorem homogeneousRowsPrefixMemory_read [BN254.FieldCertificate]
    (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase) (n rows : Nat) (base : Memory)
    (inside : n ≤ rows) (separate : HomogeneousRegionsDisjoint base rows) (i : Nat)
    (valid : i < 3 * (rows - 1)) :
    (homogeneousRowsPrefixMemory points scales n base).ram (base.registers 10 + BitVec.ofNat 256 i) =
      base.ram (base.registers 10 + BitVec.ofNat 256 i) ∧
    (homogeneousRowsPrefixMemory points scales n base).ram (base.registers 11 + BitVec.ofNat 256 i) =
      base.ram (base.registers 11 + BitVec.ofNat 256 i) := by
  rw [homogeneousRowsPrefixMemory_ram]
  constructor
  · apply storeDrawWords_disjoint
    intro j bound
    rw [homogeneousRowsWords_length] at bound
    simpa only [Nat.zero_add] using (separate i valid j (by omega)).1
  · apply storeDrawWords_disjoint
    intro j bound
    rw [homogeneousRowsWords_length] at bound
    simpa only [Nat.zero_add] using (separate i valid j (by omega)).2

/-- Every row prefix retains the next canonical scale word. -/
theorem homogeneousRowsPrefixMemory_scale [BN254.FieldCertificate]
    (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase) (n rows : Nat) (base : Memory)
    (inside : n ≤ rows) (separate : HomogeneousRegionsDisjoint base rows) (i : Nat)
    (valid : i < 3 * (rows - 1))
    (source : base.ram (base.registers 11 + BitVec.ofNat 256 i) = BitVec.ofNat 256 (scales i).value.val) :
    (homogeneousRowsPrefixMemory points scales n base).ram
      ((homogeneousRowsPrefixMemory points scales n base).registers 11 + BitVec.ofNat 256 i) =
      BitVec.ofNat 256 (scales i).value.val := by
  rw [homogeneousRowsPrefixMemory_caller _ _ _ _ 11 (by decide),
    (homogeneousRowsPrefixMemory_read points scales n rows base inside separate i (by omega)).2, source]

/-- Every row prefix retains the next canonical free point. -/
theorem homogeneousRowsPrefixMemory_point [BN254.FieldCertificate]
    (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase) (n rows : Nat) (base : Memory)
    (inside : n ≤ rows) (separate : HomogeneousRegionsDisjoint base rows) (i : Nat) (valid : i < rows)
    (positive : i ≠ 0)
    (source : StoredPointEncoding base.ram (base.registers 10 + BitVec.ofNat 256 (3 * (i - 1))) (points i)) :
    StoredPointEncoding (homogeneousRowsPrefixMemory points scales n base).ram
      ((homogeneousRowsPrefixMemory points scales n base).registers 10 + BitVec.ofNat 256 (3 * (i - 1))) (points i) := by
  rw [homogeneousRowsPrefixMemory_caller _ _ _ _ 10 (by decide)]
  have readWord (offset : Nat) (small : offset < 3) :=
    (homogeneousRowsPrefixMemory_read points scales n rows base inside separate (3 * (i - 1) + offset) (by omega)).1
  have zero := readWord 0 (by decide)
  have one : (homogeneousRowsPrefixMemory points scales n base).ram
      (base.registers 10 + BitVec.ofNat 256 (3 * (i - 1)) + 1) =
      base.ram (base.registers 10 + BitVec.ofNat 256 (3 * (i - 1)) + 1) := by
    simpa [BitVec.ofNat_add, BitVec.add_assoc] using readWord 1 (by decide)
  have two : (homogeneousRowsPrefixMemory points scales n base).ram
      (base.registers 10 + BitVec.ofNat 256 (3 * (i - 1)) + 1 + 1) =
      base.ram (base.registers 10 + BitVec.ofNat 256 (3 * (i - 1)) + 1 + 1) := by
    simpa [BitVec.ofNat_add, BitVec.add_assoc] using readWord 2 (by decide)
  simp only [Nat.add_zero] at zero
  simpa only [StoredPointEncoding, zero, one, two] using source

end Kriterion.ArgoMAC.ArithmeticSimulator
