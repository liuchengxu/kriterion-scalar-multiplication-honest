import Construction.Simulator.RangeWidth
import Proof.Privacy.Simulator.Arithmetic.WordBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Zero has no significant bits. Every positive integer has one bit beyond its base-two logarithm. -/
def bitLength (value : Nat) : Nat := if value = 0 then 0 else value.log2 + 1

/-- Division by two removes one significant bit from a positive integer. -/
theorem bitLength_step (value : Nat) (positive : 0 < value) :
    bitLength value = bitLength (value / 2) + 1 := by
  by_cases one : value = 1
  · subst value
    decide
  · have two : 2 ≤ value := by omega
    have half : 0 < value / 2 := Nat.div_pos two (by decide)
    simp only [bitLength, if_neg (Nat.ne_of_gt positive), if_neg (Nat.ne_of_gt half)]
    rw [Nat.log2_def value, if_pos two]

/-- The host contains every width instruction before the return label. -/
def ContainsRangeWidth (host : Machine) (labels : Fin 10 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 10, pc.val < 9 → host.code[(labels pc).val] =
    relocate labels (rangeWidth.code[pc.val]'(by exact pc.isLt))

/-- The actual shift instruction computes integer division by two. -/
theorem width_shift (value : Nat) (fits : value < 2 ^ 256) :
    BitVec.ofNat 256 value >>> (1 : Nat) = BitVec.ofNat 256 (value / 2) := by
  apply BitVec.eq_of_toNat_eq
  have half : value / 2 < 2 ^ 256 := lt_of_le_of_lt (Nat.div_le_self _ _) fits
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits,
    Nat.mod_eq_of_lt half, Nat.shiftRight_eq_div_pow, pow_one]

/-- Each width iteration increments the count and shifts the remaining value. -/
theorem widthBlock_step [BN254.FieldCertificate] (host : Machine) (fuel count value : Nat)
    (labels : Fin 10 → Fin (host.size + 1)) (present : ContainsRangeWidth host labels)
    (base : Memory) (positive : 0 < value) (fits : value < 2 ^ 256) :
    runPrefix host (fuel + 3) ⟨labels 4, frame base 0 count (BitVec.ofNat 256 value)⟩ =
      (runPrefix host fuel ⟨labels 4, frame base 0 (count + 1) (BitVec.ofNat 256 (value / 2))⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 3)) := by
  have nonzero : BitVec.ofNat 256 value ≠ 0#256 := by
    intro equal
    have natural := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] at natural
    change value = 0 at natural
    omega
  have nextCount : BitVec.ofNat 256 count + 1#256 = BitVec.ofNat 256 (count + 1) := by
    rw [BitVec.ofNat_add]
  simp [runPrefix, step, present 4 (by decide), present 5 (by decide), present 6 (by decide),
    rangeWidth, relocate, frame, Arithmetic.eval, nonzero, nextCount, width_shift value fits,
    PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc, Function.update_comm]

/-- The width loop reaches its exit with the exact bit count and instruction cost. -/
theorem widthBlock_loop [BN254.FieldCertificate] (host : Machine) (value count : Nat)
    (labels : Fin 10 → Fin (host.size + 1)) (present : ContainsRangeWidth host labels)
    (base : Memory) (fits : value < 2 ^ 256) :
    runPrefix host (3 * bitLength value + 1) ⟨labels 4, frame base 0 count (BitVec.ofNat 256 value)⟩ =
      PMF.pure (some (false, ⟨labels 7, frame base 0 (count + bitLength value) 0⟩,
        3 * bitLength value + 1)) := by
  induction value using Nat.strong_induction_on generalizing count with
  | h value ih =>
      by_cases zero : value = 0
      · subst value
        simp [bitLength, runPrefix, step, present 4 (by decide), rangeWidth, relocate, frame, PMF.pure_map]
      · have positive : 0 < value := by omega
        have shorter : value / 2 < value := Nat.div_lt_self positive (by decide)
        have length := bitLength_step value positive
        rw [show 3 * bitLength value + 1 = (3 * bitLength (value / 2) + 1) + 3 by omega,
          widthBlock_step host (3 * bitLength (value / 2) + 1) count value labels present base positive fits,
          ih (value / 2) shorter (count + 1) (lt_trans shorter fits)]
        simp [PMF.pure_map, length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Four instructions initialize the width loop from the runtime range register. -/
theorem widthBlock_setup [BN254.FieldCertificate] (host : Machine) (fuel : Nat)
    (labels : Fin 10 → Fin (host.size + 1)) (present : ContainsRangeWidth host labels) (base : Memory) :
    runPrefix host (fuel + 4) ⟨labels 0, base⟩ =
      (runPrefix host fuel ⟨labels 4, frame base 0 0 (base.registers 5)⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 4)) := by
  simp [runPrefix, step, present 0 (by decide), present 1 (by decide), present 2 (by decide),
    present 3 (by decide), rangeWidth, relocate, frame, Arithmetic.eval,
    Function.update_comm, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The zero word represents the full 256-bit range. -/
def runtimeRange (bound : Word) : Nat := if bound = 0#256 then 2 ^ 256 else bound.toNat

/-- The low-word sampler uses at most 256 bits. -/
def lowWidth (bound : Word) : Nat := if bound = 0#256 then 256 else bitLength bound.toNat

/-- This count charges every width-loop instruction before the return label. -/
def widthCost (bound : Word) : Nat := if bound = 0#256 then 7 else 3 * bitLength bound.toNat + 6

/-- Every nonzero word encodes a positive integer. -/
theorem word_positive (bound : Word) (nonzero : bound ≠ 0#256) : 0 < bound.toNat := by
  by_contra notPositive
  have zero : bound.toNat = 0 := by omega
  apply nonzero
  exact BitVec.eq_of_toNat_eq zero

/-- Every encoded runtime range is positive and fits in one full word range. -/
theorem runtimeRange_bounds (bound : Word) : 0 < runtimeRange bound ∧ runtimeRange bound ≤ 2 ^ 256 := by
  unfold runtimeRange
  split
  · exact ⟨by decide, le_rfl⟩
  · rename_i nonzero
    exact ⟨word_positive bound nonzero, Nat.le_of_lt bound.isLt⟩

/-- The encoded range uses no more than 256 low bits. -/
theorem lowWidth_bound (bound : Word) : lowWidth bound ≤ 256 := by
  unfold lowWidth
  split
  · exact le_rfl
  · rename_i nonzero
    have positive := word_positive bound nonzero
    have logarithm := (Nat.log2_lt (Nat.ne_of_gt positive)).mpr bound.isLt
    simp only [bitLength, if_neg (Nat.ne_of_gt positive)]
    omega

/-- The ordinary range exits the width routine after one branch. -/
theorem widthBlock_narrow_tail [BN254.FieldCertificate] (host : Machine) (count : Nat)
    (labels : Fin 10 → Fin (host.size + 1)) (present : ContainsRangeWidth host labels)
    (base : Memory) (nonzero : base.registers 5 ≠ 0#256) :
    runPrefix host 1 ⟨labels 7, frame base 0 count 0⟩ =
      PMF.pure (some (false, ⟨labels 9, frame base 0 count 0⟩, 1)) := by
  simp [runPrefix, step, present 7 (by decide), rangeWidth, relocate, frame, nonzero, PMF.pure_map]

/-- The full-word range installs a low-bit count of 256. -/
theorem widthBlock_full_tail [BN254.FieldCertificate] (host : Machine) (count : Nat)
    (labels : Fin 10 → Fin (host.size + 1)) (present : ContainsRangeWidth host labels)
    (base : Memory) (zero : base.registers 5 = 0#256) :
    runPrefix host 2 ⟨labels 7, frame base 0 count 0⟩ =
      PMF.pure (some (false, ⟨labels 9, frame base 0 256 0⟩, 2)) := by
  simp [runPrefix, step, present 7 (by decide), present 8 (by decide), rangeWidth, relocate,
    frame, zero, PMF.pure_map, Function.update_comm]

/-- The runtime width routine prepares the exact sampling-loop frame. -/
theorem widthBlock_run [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 10 → Fin (host.size + 1)) (present : ContainsRangeWidth host labels) (base : Memory) :
    runPrefix host (widthCost (base.registers 5)) ⟨labels 0, base⟩ =
      PMF.pure (some (false, ⟨labels 9, frame base 0 (lowWidth (base.registers 5)) 0⟩,
        widthCost (base.registers 5))) := by
  let count := bitLength (base.registers 5).toNat
  let tailCost := if base.registers 5 = 0#256 then 2 else 1
  have countCost : widthCost (base.registers 5) = (3 * count + 1 + tailCost) + 4 := by
    by_cases zero : base.registers 5 = 0#256
    · simp [widthCost, count, tailCost, zero, bitLength]
    · simp only [widthCost, tailCost, if_neg zero, count]
  rw [countCost, widthBlock_setup host (3 * count + 1 + tailCost) labels present base]
  have represented : base.registers 5 = BitVec.ofNat 256 (base.registers 5).toNat := by simp
  have loop := widthBlock_loop host (base.registers 5).toNat 0 labels present base (base.registers 5).isLt
  rw [show 3 * count + 1 + tailCost = (3 * count + 1) + tailCost from rfl, prefix_add]
  conv_lhs => arg 2; arg 1; rw [represented]
  rw [loop]
  simp only [PMF.pure_bind, Nat.zero_add]
  by_cases zero : base.registers 5 = 0#256
  · simp only [tailCost, if_pos zero]
    change ((runPrefix host 2 ⟨labels 7, frame base 0 count 0⟩).map _).map _ = _
    rw [widthBlock_full_tail host count labels present base zero]
    simp [PMF.pure_map, lowWidth, widthCost, count, tailCost, zero, bitLength]
  · simp only [tailCost, if_neg zero]
    change ((runPrefix host 1 ⟨labels 7, frame base 0 count 0⟩).map _).map _ = _
    rw [widthBlock_narrow_tail host count labels present base zero]
    simp only [PMF.pure_map, Option.map_some, lowWidth, if_neg zero, count, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The runtime encoding recovers the original bound word. -/
theorem runtimeRange_word (bound : Word) : BitVec.ofNat 256 (runtimeRange bound) = bound := by
  by_cases zero : bound = 0#256
  · subst bound
    simp only [runtimeRange, ite_true]
    decide
  · simp only [runtimeRange, if_neg zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Only the zero bound encodes the full word range. -/
theorem runtimeRange_full (bound : Word) : runtimeRange bound = 2 ^ 256 ↔ bound = 0#256 := by
  unfold runtimeRange
  split
  · simp_all
  · rename_i nonzero
    have smaller := bound.isLt
    simp only [nonzero, iff_false]
    omega

/-- The width agrees with the source sampler's low-word width. -/
theorem lowWidth_source (bound : Word) : lowWidth bound = min ((runtimeRange bound).log2 + 1) 256 := by
  by_cases zero : bound = 0#256
  · simp only [lowWidth, runtimeRange, if_pos zero, Nat.log2_two_pow]
    rfl
  · have positive := word_positive bound zero
    have fits := lowWidth_bound bound
    simp only [lowWidth, if_neg zero, bitLength, if_neg (Nat.ne_of_gt positive)] at fits
    simp only [lowWidth, runtimeRange, if_neg zero, bitLength, if_neg (Nat.ne_of_gt positive), Nat.min_eq_left fits]

/-- The width routine reserves at most 774 instructions before its return. -/
theorem widthCost_bound (bound : Word) : widthCost bound ≤ 774 := by
  by_cases zero : bound = 0#256
  · simp only [widthCost, if_pos zero]
    omega
  · have fits := lowWidth_bound bound
    simp only [lowWidth, if_neg zero] at fits
    simp only [widthCost, if_neg zero]
    omega

end Kriterion.ArgoMAC.ArithmeticSimulator
