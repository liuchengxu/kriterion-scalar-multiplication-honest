import Construction.Simulator.HashProgram
import Proof.Privacy.Simulator.Arithmetic.HashHandlerSource
import Proof.Privacy.Simulator.Arithmetic.HashOutput
import Proof.Privacy.Simulator.Arithmetic.PairMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The fixed target load implements its memory source exactly. -/
theorem hashProgramTarget_memory (memory : Memory) :
    executeLinear hashProgramTarget memory = hashProgramTargetMemory memory := by
  simp [executeLinear, hashProgramTarget, hashProgramTargetMemory, LinearInstruction.execute]

/-- The hash programming block uses forty-seven fixed instructions. -/
theorem hashProgram_length : hashProgram.length = 47 := by rfl

/-- The compiled hash programming block implements its full memory source. -/
theorem hashProgram_memory (memory : Memory) : executeLinear hashProgram memory = hashProgrammed memory := by
  simp only [hashProgram, executeLinear_append, oracleLoad_memory, hashSetup_memory,
    hashProgramTarget_memory, hashInstall_memory, oracleCommit_memory, hashProgrammed]

/-- The programming block returns to any host after its exact charge. -/
theorem hashProgram_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host hashProgram labels)
    (memory : Memory) (fuel : Nat) :
    run host (47 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 47, hashProgrammed memory⟩).map
        (Option.map fun result => (result.1, result.2 + 47)) := by
  simpa only [hashProgram_length, hashProgram_memory] using
    linear_continue host hashProgram labels present memory fuel

/-- The final count commit preserves every represented pair outside the header. -/
theorem oracleCommitted_pairs (memory : Memory) (pairs : List (Word × Word)) (address : Word)
    (represented : RepresentsPairs memory.ram address pairs)
    (headerSafe : ∀ index, index < 2 * pairs.length →
      address + BitVec.ofNat 256 index ≠ memory.ram 13) :
    RepresentsPairs (oracleCommitted memory).ram address pairs := by
  apply RepresentsPairs.congr pairs memory.ram _ address represented
  intro index bound
  change Function.update memory.ram (memory.ram 13) (memory.registers 0)
    (address + BitVec.ofNat 256 index) = _
  exact Function.update_of_ne (headerSafe index bound) _ _

/-- The programmed hash stores its target as the first matching pair. -/
theorem hashProgrammed_pairs (memory : Memory) (pairs : List (Word × Word))
    (represented : RepresentsPairs (oracleLoaded memory).ram ((oracleLoaded memory).registers 1) pairs)
    (fits : 2 * pairs.length + 2 ≤ 2 ^ 256)
    (headerSafe : ∀ index, index < 2 * (pairs.length + 1) →
      (hashInstalled (hashProgramTargetMemory (hashReady (oracleLoaded memory)))).registers 1 +
        BitVec.ofNat 256 index ≠
          (hashInstalled (hashProgramTargetMemory (hashReady (oracleLoaded memory)))).ram 13) :
    RepresentsPairs (hashProgrammed memory).ram
      ((hashInstalled (hashProgramTargetMemory (hashReady (oracleLoaded memory)))).registers 1)
      (((oracleLoaded memory).registers 8, (oracleLoaded memory).ram 14) :: pairs) := by
  apply oracleCommitted_pairs
  · have inserted := hashInstalled_represents (hashProgramTargetMemory (hashReady (oracleLoaded memory)))
      pairs (by simpa [hashProgramTargetMemory, hashReady] using represented) fits
    simpa [hashProgramTargetMemory, hashReady] using inserted
  · simpa using headerSafe

end Kriterion.ArgoMAC.ArithmeticSimulator
