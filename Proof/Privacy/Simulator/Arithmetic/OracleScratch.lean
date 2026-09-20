import Construction.Simulator.OracleScratch
import Proof.Privacy.Simulator.Arithmetic.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The save instructions have the exact scratch-memory effect. -/
theorem oracleSave_memory (memory : Memory) : executeLinear oracleSave memory = oracleSaved memory := by
  simp [executeLinear, oracleSave, LinearInstruction.execute, oracleSaved, Function.update_comm]

/-- The restore instructions have the exact register effect. -/
theorem oracleRestore_memory (memory : Memory) :
    executeLinear oracleRestore memory = oracleRestored memory := by
  simp [executeLinear, oracleRestore, LinearInstruction.execute, Arithmetic.eval,
    oracleRestored, Function.update_comm]

/-- Each saved metadata register occupies its corresponding scratch cell. -/
theorem oracleSaved_metadata (memory : Memory) (index : Fin 6) :
    (oracleSaved memory).ram (BitVec.ofNat 256 index.val) = memory.registers ⟨index.val, by omega⟩ := by
  fin_cases index <;> simp [oracleSaved]

/-- Scratch cell six retains the inverse position. -/
theorem oracleSaved_position (memory : Memory) :
    (oracleSaved memory).ram 6 = memory.registers 8 := by simp [oracleSaved]

/-- The save block preserves every RAM cell outside its seven-cell scratch region. -/
theorem oracleSaved_other (memory : Memory) (address : Word) (outside : 7 ≤ address.toNat) :
    (oracleSaved memory).ram address = memory.ram address := by
  have different (index : Fin 7) : address ≠ BitVec.ofNat 256 index.val := by
    intro equal
    have values := congrArg BitVec.toNat equal
    have small := index.isLt
    have bound : index.val < 2 ^ 256 := lt_trans small (by decide)
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at values
    omega
  have d0 : address ≠ 0#256 := different ⟨0, by decide⟩
  have d1 : address ≠ 1#256 := different ⟨1, by decide⟩
  have d2 : address ≠ 2#256 := different ⟨2, by decide⟩
  have d3 : address ≠ 3#256 := different ⟨3, by decide⟩
  have d4 : address ≠ 4#256 := different ⟨4, by decide⟩
  have d5 : address ≠ 5#256 := different ⟨5, by decide⟩
  have d6 : address ≠ 6#256 := different ⟨6, by decide⟩
  simp [oracleSaved, d0, d1, d2, d3, d4, d5, d6]

/-- Restoration recovers each saved metadata value after a sampler call. -/
theorem oracleRestored_metadata (original current : Memory) (index : Fin 6) :
    (oracleRestored {current with ram := (oracleSaved original).ram}).registers
      ⟨index.val, by omega⟩ = original.registers ⟨index.val, by omega⟩ := by
  fin_cases index <;> simp [oracleRestored, oracleSaved]

/-- Restoration preserves the sampler's value and flag and restores the inverse position. -/
theorem oracleRestored_sample (original current : Memory) :
    let final := oracleRestored {current with ram := (oracleSaved original).ram}
    final.registers 9 = current.registers 0 ∧
      final.registers 7 = current.registers 7 ∧ final.registers 8 = original.registers 8 := by
  simp [oracleRestored, oracleSaved]

/-- The save block returns after fourteen fixed instructions. -/
theorem oracleSave_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host oracleSave labels)
    (memory : Memory) (fuel : Nat) :
    run host (14 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 14, oracleSaved memory⟩).map
        (Option.map fun result => (result.1, result.2 + 14)) := by
  have length : oracleSave.length = 14 := rfl
  simpa only [oracleSave_memory, length] using linear_continue host oracleSave labels present memory fuel

/-- The restore block returns after sixteen fixed instructions. -/
theorem oracleRestore_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host oracleRestore labels)
    (memory : Memory) (fuel : Nat) :
    run host (16 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 16, oracleRestored memory⟩).map
        (Option.map fun result => (result.1, result.2 + 16)) := by
  have length : oracleRestore.length = 16 := rfl
  simpa only [oracleRestore_memory, length] using linear_continue host oracleRestore labels present memory fuel

end Kriterion.ArgoMAC.ArithmeticSimulator
