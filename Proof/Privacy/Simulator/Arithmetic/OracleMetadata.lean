import Construction.Simulator.OracleMetadata
import Proof.Privacy.Simulator.Arithmetic.LinearProgram
import Proof.Privacy.Simulator.Arithmetic.MemoryLayout
import Proof.Privacy.Simulator.OperationalOracle

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The first ten loader instructions compute the header and save the query metadata. -/
theorem oracleLoadSetup_memory (memory : Memory) :
    executeLinear oracleLoadSetup memory = oracleLoadInitial memory := by
  simp [executeLinear, oracleLoadSetup, LinearInstruction.execute, Arithmetic.eval,
    oracleLoadInitial, oracleLoadRam, oracleHeader, Function.update_comm]

/-- The final twelve loader instructions compute the source metadata. -/
theorem oracleLoadFinish_memory (memory : Memory) :
    executeLinear oracleLoadFinish (oracleLoadInitial memory) = oracleLoaded memory := by
  simp [executeLinear, oracleLoadFinish, LinearInstruction.execute, Arithmetic.eval,
    oracleLoadInitial, oracleLoaded, Function.update_comm]

/-- The loader implements the complete metadata source in twenty-two fixed instructions. -/
theorem oracleLoad_memory (memory : Memory) : executeLinear oracleLoad memory = oracleLoaded memory := by
  unfold oracleLoad executeLinear
  rw [List.foldl_append]
  change executeLinear oracleLoadFinish (executeLinear oracleLoadSetup memory) = _
  rw [oracleLoadSetup_memory, oracleLoadFinish_memory]

/-- The commit block implements the complete persistent-header update. -/
theorem oracleCommit_memory (memory : Memory) :
    executeLinear oracleCommit memory = oracleCommitted memory := by
  simp [executeLinear, oracleCommit, LinearInstruction.execute, oracleCommitted, Function.update_comm]

/-- The fixed arithmetic header address agrees with the global memory layout. -/
theorem oracleHeader_address (oracle : Fin 15749) :
    oracleHeader (BitVec.ofNat 256 oracle.val) = oracleAddress oracle 0 0 := by
  simp [oracleHeader, oracleAddress, oracleCell, BitVec.ofNat_add, BitVec.ofNat_mul]

/-- Scratch writes cannot alter the selected public used-count header. -/
theorem oracleLoadRam_header (memory : Memory) (oracle : Fin 15749)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val) :
    oracleLoadRam memory (oracleHeader (memory.registers 9)) =
      memory.ram (oracleAddress oracle 0 0) := by
  have d9 : oracleAddress oracle 0 0 ≠ 9#256 :=
    oracleAddress_private_disjoint oracle 0 0 9 (by decide) (by decide)
  have d12 : oracleAddress oracle 0 0 ≠ 12#256 :=
    oracleAddress_private_disjoint oracle 0 0 12 (by decide) (by decide)
  have d13 : oracleAddress oracle 0 0 ≠ 13#256 :=
    oracleAddress_private_disjoint oracle 0 0 13 (by decide) (by decide)
  simp [oracleLoadRam, index, oracleHeader_address, d9, d12, d13]

/-- The loaded count equals the persistent public header. -/
theorem oracleLoaded_used (memory : Memory) (oracle : Fin 15749)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val) :
    (oracleLoaded memory).registers 0 = memory.ram (oracleAddress oracle 0 0) := by
  simpa [oracleLoaded] using oracleLoadRam_header memory oracle index

/-- The loader preserves the query operand and records its global index and tag. -/
theorem oracleLoaded_query (memory : Memory) :
    (oracleLoaded memory).registers 8 = memory.registers 8 ∧
    (oracleLoaded memory).ram 9 = memory.registers 9 ∧
    (oracleLoaded memory).ram 12 = memory.registers 10 ∧
    (oracleLoaded memory).ram 13 = oracleHeader (memory.registers 9) := by
  simp [oracleLoaded, oracleLoadRam]

/-- The loader returns after twenty-two charged instructions. -/
theorem oracleLoad_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host oracleLoad labels)
    (memory : Memory) (fuel : Nat) :
    run host (22 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 22, oracleLoaded memory⟩).map
        (Option.map fun result => (result.1, result.2 + 22)) := by
  have length : oracleLoad.length = 22 := rfl
  simpa only [oracleLoad_memory, length] using linear_continue host oracleLoad labels present memory fuel

/-- The persistent-header commit returns after three charged instructions. -/
theorem oracleCommit_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host oracleCommit labels)
    (memory : Memory) (fuel : Nat) :
    run host (3 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 3, oracleCommitted memory⟩).map
        (Option.map fun result => (result.1, result.2 + 3)) := by
  have length : oracleCommit.length = 3 := rfl
  simpa only [oracleCommit_memory, length] using linear_continue host oracleCommit labels present memory fuel

/-- Every fresh sparse update preserves equality between both list lengths and the used count. -/
theorem sparsePermutation_extend_lengths {size : Nat}
    (state : Security.OperationalOracle.SparsePermutation size) (room : state.used < size)
    (input output : Fin size) (inputLength : state.inputs.length = state.used)
    (outputLength : state.outputs.length = state.used) :
    (state.extend room input output).inputs.length = (state.extend room input output).used ∧
      (state.extend room input output).outputs.length = (state.extend room input output).used := by
  simp [Security.OperationalOracle.SparsePermutation.extend, inputLength, outputLength]

end Kriterion.ArgoMAC.ArithmeticSimulator
