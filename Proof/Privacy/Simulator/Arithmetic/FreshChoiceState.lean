import Proof.Privacy.Simulator.Arithmetic.FreshChoice
import Proof.Privacy.Simulator.Arithmetic.TotalSamplerMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The accepted suffix size has the exact runtime range encoding. -/
theorem unusedRange (size used : Nat) (room : used < size) (fits : size ≤ 2 ^ 256) :
    runtimeRange (BitVec.ofNat 256 size - BitVec.ofNat 256 used) = size - used := by
  rw [BitVec.ofNat_sub_ofNat_of_le size used (lt_of_lt_of_le room fits) (Nat.le_of_lt room)]
  exact runtimeRange_nat (size - used) (by omega) (by omega)

/-- The fresh path restores every metadata register after every retry outcome. -/
theorem freshChoice_metadata (attempts : Nat) (original sampled : Memory) (cost : Nat)
    (supported : (sampled, cost) ∈ (freshChoiceSamples attempts original).support) (index : Fin 6) :
    (freshChoiceFinal sampled).registers ⟨index.val, by omega⟩ =
      original.registers ⟨index.val, by omega⟩ := by
  have same := (runtimeSamplerMemory_data _ _ _ sampled cost supported).2
  have saved : sampled.ram = (oracleSaved original).ram := same
  by_cases failed : sampled.registers 7 = 0#256 <;>
    fin_cases index <;> simp [freshChoiceFinal, oracleRestored, saved, oracleSaved, failed]

/-- The fresh path retains the inverse input position. -/
theorem freshChoice_position (attempts : Nat) (original sampled : Memory) (cost : Nat)
    (supported : (sampled, cost) ∈ (freshChoiceSamples attempts original).support) :
    (freshChoiceFinal sampled).registers 8 = original.registers 8 := by
  have same := (runtimeSamplerMemory_data _ _ _ sampled cost supported).2
  have saved : sampled.ram = (oracleSaved original).ram := same
  by_cases failed : sampled.registers 7 = 0#256 <;>
    simp [freshChoiceFinal, oracleRestored, saved, oracleSaved, failed]

/-- The fresh path preserves all permanent RAM cells outside scratch zero through seven. -/
theorem freshChoice_ram (attempts : Nat) (original sampled : Memory) (cost : Nat)
    (supported : (sampled, cost) ∈ (freshChoiceSamples attempts original).support)
    (address : Word) (outside : 8 ≤ address.toNat) :
    (freshChoiceFinal sampled).ram address = original.ram address := by
  have same := (runtimeSamplerMemory_data _ _ _ sampled cost supported).2
  have saved : sampled.ram = (oracleSaved original).ram := same
  have different : address ≠ 7#256 := by
    intro equal
    subst address
    norm_num at outside
  by_cases failed : sampled.registers 7 = 0#256 <;>
    simp [freshChoiceFinal, oracleRestored, saved, different, failed,
      oracleSaved_other original address (by omega)]

/-- The fresh path preserves all four stacks. -/
theorem freshChoice_bits (attempts : Nat) (original sampled : Memory) (cost : Nat)
    (supported : (sampled, cost) ∈ (freshChoiceSamples attempts original).support) :
    (freshChoiceFinal sampled).bits = original.bits := by
  have unchanged := (runtimeSamplerMemory_data _ _ _ sampled cost supported).1
  by_cases failed : sampled.registers 7 = 0#256 <;>
    simpa [freshChoiceFinal, oracleRestored, freshChoiceInitial, oracleSaved, failed] using unchanged

/-- Every accepted chosen position lies in the unused suffix. -/
theorem freshChoice_chosen_bounds [BN254.FieldCertificate]
    (attempts size used : Nat) (memory : Memory) (chosen : Word)
    (room : used < size) (fits : size ≤ 2 ^ 256)
    (sizeWord : memory.registers 5 = BitVec.ofNat 256 size)
    (usedWord : memory.registers 0 = BitVec.ofNat 256 used)
    (supported : some chosen ∈ ((freshChoiceSamples attempts memory).map
      (fun result => freshChoiceValue (freshChoiceFinal result.1))).support) :
    used ≤ chosen.toNat ∧ chosen.toNat < size := by
  rw [freshChoiceSamples_source, sizeWord, usedWord, unusedRange size used room fits] at supported
  obtain ⟨draw, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases draw with
  | none => simp at equal
  | some rank =>
      simp only [Option.map_some, Option.some.injEq] at equal
      subst chosen
      have bounded : rank.val + used < 2 ^ 256 := lt_of_lt_of_le (by have h := rank.isLt; omega) fits
      have value : (BitVec.ofNat 256 rank.val + BitVec.ofNat 256 used).toNat = rank.val + used := by
        rw [← BitVec.ofNat_add]
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
      rw [value]
      have h := rank.isLt
      omega

end Kriterion.ArgoMAC.ArithmeticSimulator
