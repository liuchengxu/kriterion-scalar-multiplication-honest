import Construction.Simulator.OverlayMetadata
import Proof.Privacy.Simulator.Arithmetic.PairStore
import Proof.Privacy.Simulator.Arithmetic.HashOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The overlay loader implements its memory source exactly. -/
theorem overlayLoad_memory (memory : Memory) : executeLinear overlayLoad memory = overlayLoaded memory := by
  simp [executeLinear, overlayLoad, overlayLoaded, overlayHeader, LinearInstruction.execute, Arithmetic.eval, Function.update_comm]

/-- The reverse setup implements its memory source exactly. -/
theorem overlayReverseSetup_memory (memory : Memory) :
    executeLinear overlayReverseSetup memory = overlayReverseReady memory := by
  simp [executeLinear, overlayReverseSetup, overlayReverseReady,
    LinearInstruction.execute, Arithmetic.eval, Function.update_comm]

/-- The inverse loader implements both fixed instruction lists exactly. -/
theorem overlayInverseLoad_memory (memory : Memory) :
    executeLinear overlayInverseLoad memory = overlayInverseLoaded memory := by
  simp only [overlayInverseLoad, executeLinear_append, overlayLoad_memory,
    overlayReverseSetup_memory, overlayInverseLoaded]

/-- The host executes the inverse loader before its continuation. -/
theorem overlayInverseLoad_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host overlayInverseLoad labels)
    (memory : Memory) (fuel : Nat) :
    run host (9 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 9, overlayInverseLoaded memory⟩).map
        (Option.map fun result => (result.1, result.2 + 9)) := by
  simpa only [overlayInverseLoad_memory, show overlayInverseLoad.length = 9 from rfl] using
    linear_continue host overlayInverseLoad labels present memory fuel

/-- The query restore block implements its memory source exactly. -/
theorem queryRestore_memory (memory : Memory) : executeLinear queryRestore memory = queryRestored memory := by
  simp [executeLinear, queryRestore, queryRestored, LinearInstruction.execute, Function.update_comm]

/-- The append setup implements its memory source exactly. -/
theorem overlayAppendSetup_memory (memory : Memory) :
    executeLinear overlayAppendSetup memory = overlayAppendReady memory := by
  simp [executeLinear, overlayAppendSetup, overlayAppendReady, overlayHeader,
    LinearInstruction.execute, Arithmetic.eval, Function.update_comm]

/-- The append finish implements its memory source exactly. -/
theorem overlayAppendFinish_memory (memory : Memory) :
    executeLinear overlayAppendFinish memory = overlayAppendFinished memory := by
  simp [executeLinear, overlayAppendFinish, overlayAppendFinished, LinearInstruction.execute, Arithmetic.eval, Function.update_comm]

/-- The complete append block implements its memory source exactly. -/
theorem overlayAppend_memory (memory : Memory) : executeLinear overlayAppend memory = overlayAppended memory := by
  simp only [overlayAppend, executeLinear_append, overlayAppendSetup_memory, pairStore_memory,
    overlayAppendFinish_memory, overlayAppended]

/-- The loader preserves the RAM, stacks, query operand, and acceptance flag. -/
theorem overlayLoaded_data (memory : Memory) :
    (overlayLoaded memory).ram = memory.ram ∧ (overlayLoaded memory).bits = memory.bits ∧
    (overlayLoaded memory).registers 8 = memory.registers 8 ∧
    (overlayLoaded memory).registers 7 = memory.registers 7 := by
  simp [overlayLoaded]

/-- The append block preserves the current answer, header, acceptance flag, and stacks. -/
theorem overlayAppended_data (memory : Memory) :
    (overlayAppended memory).registers 8 = memory.registers 8 ∧
    (overlayAppended memory).registers 6 = memory.registers 6 ∧
    (overlayAppended memory).registers 7 = memory.registers 7 ∧
    (overlayAppended memory).bits = memory.bits := by
  simp [overlayAppended, overlayAppendFinished, pairStored, overlayAppendReady]

/-- The host executes the loader before its continuation. -/
theorem overlayLoad_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host overlayLoad labels)
    (memory : Memory) (fuel : Nat) :
    run host (5 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 5, overlayLoaded memory⟩).map
        (Option.map fun result => (result.1, result.2 + 5)) := by
  simpa only [overlayLoad_memory, show overlayLoad.length = 5 from rfl] using
    linear_continue host overlayLoad labels present memory fuel

/-- The host executes the query restore block before its continuation. -/
theorem queryRestore_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host queryRestore labels)
    (memory : Memory) (fuel : Nat) :
    run host (4 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 4, queryRestored memory⟩).map
        (Option.map fun result => (result.1, result.2 + 4)) := by
  simpa only [queryRestore_memory, show queryRestore.length = 4 from rfl] using
    linear_continue host queryRestore labels present memory fuel

/-- The host executes all seventeen append instructions before its continuation. -/
theorem overlayAppend_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host overlayAppend labels)
    (memory : Memory) (fuel : Nat) :
    run host (17 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 17, overlayAppended memory⟩).map
        (Option.map fun result => (result.1, result.2 + 17)) := by
  simpa only [overlayAppend_memory, show overlayAppend.length = 17 from rfl] using
    linear_continue host overlayAppend labels present memory fuel

end Kriterion.ArgoMAC.ArithmeticSimulator
