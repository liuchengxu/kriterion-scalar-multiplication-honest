import Construction.Simulator.InstallFresh
import Proof.Privacy.Simulator.Arithmetic.PairMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The thirty fixed instructions have the exact installation effect. -/
theorem installFresh_memory (memory : Memory) :
    executeLinear installFresh memory = installedFresh memory := by
  simp [executeLinear, installFresh, pairStore, LinearInstruction.execute, Arithmetic.eval,
    installedFresh, Function.update_comm, Function.update_eq_self]
  funext register
  fin_cases register <;> simp

/-- Installation advances both sparse tables and the used prefix. -/
theorem installedFresh_metadata (memory : Memory) :
    (installedFresh memory).registers 0 = memory.registers 0 + 1#256 ∧
    (installedFresh memory).registers 1 = memory.registers 1 - 2#256 ∧
    (installedFresh memory).registers 2 = memory.registers 2 + 1#256 ∧
    (installedFresh memory).registers 3 = memory.registers 3 - 2#256 ∧
    (installedFresh memory).registers 4 = memory.registers 4 + 1#256 ∧
    (installedFresh memory).registers 8 = memory.registers 8 := by
  simp [installedFresh]

/-- Installation preserves the query's acceptance flag and all stacks. -/
theorem installedFresh_frame (memory : Memory) :
    (installedFresh memory).registers 5 = memory.registers 5 ∧
    (installedFresh memory).registers 7 = memory.registers 7 ∧
    (installedFresh memory).bits = memory.bits := by
  simp [installedFresh]

/-- The installation leaves every other RAM cell unchanged. -/
theorem installedFresh_other (memory : Memory) (address : Word)
    (inputLeft : address ≠ memory.registers 1 - 2#256)
    (inputRight : address ≠ memory.registers 1 - 2#256 + 1#256)
    (outputLeft : address ≠ memory.registers 3 - 2#256)
    (outputRight : address ≠ memory.registers 3 - 2#256 + 1#256) :
    (installedFresh memory).ram address = memory.ram address := by
  simp [installedFresh, inputLeft, inputRight, outputLeft, outputRight]

/-- The installation returns after thirty actual machine instructions. -/
theorem installFresh_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host installFresh labels)
    (memory : Memory) (fuel : Nat) :
    run host (30 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 30, installedFresh memory⟩).map
        (Option.map fun result => (result.1, result.2 + 30)) := by
  have length : installFresh.length = 30 := rfl
  simpa only [installFresh_memory, length] using linear_continue host installFresh labels present memory fuel

end Kriterion.ArgoMAC.ArithmeticSimulator
