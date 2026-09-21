import Proof.Privacy.Simulator.Arithmetic.CompiledMachine
import Proof.Privacy.Simulator.Arithmetic.OnlineLazyExecution
import Proof.Privacy.Simulator.Arithmetic.SharedParsedGame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
noncomputable section

/-- The online phase receives the request body and an empty response stack. -/
def compiledOnlineMemory (memory : Memory) (body : List Bool) : Memory :=
  {memory with bits := Function.update (Function.update memory.bits 0 body) 3 []}

set_option backward.isDefEq.respectTransparency false in
/-- The online parser retains the exact labels and shared oracle. -/
theorem lazyCompiledMachine_onlineParsed [FieldCertificate] [GroupCertificate]
    (memory : Memory) (input : AffineInput) (value : Option Point)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    lazyParsedOnline lazyCompiledMachine memory input value oracle =
      (lazyOnlineResult (compiledOnlineMemory memory (affine input ++ output value)) input value oracle).map
        (fun result => result.bind fun result =>
          (words 128 508 (result.1.bits 3)).map fun labels => (labels, result.2.1)) := by
  let body := affine input ++ output value
  let inputMemory : Memory :=
    {memory with bits := Function.update (Function.update memory.bits 0 ([false, true] ++ body)) 3 []}
  have wire : inputMemory.bits 0 = false :: true :: body := by simp [inputMemory]
  have prepared : phaseDispatchMemory inputMemory body = compiledOnlineMemory memory body := by
    simp [phaseDispatchMemory, inputMemory, compiledOnlineMemory,
      Function.update_comm (show (0 : Fin 4) ≠ 3 by decide)]
  have executed := lazyCompiledMachine_onlineRun inputMemory body wire oracle
  rw [prepared] at executed
  have zero (size : Nat) : (⟨0, Nat.zero_lt_succ size⟩ : Fin (size + 1)) = 0 := by
    apply Fin.ext
    simp
  have online := lazyOnlineMachine_run (compiledOnlineMemory memory body) input value oracle
    (by simp [compiledOnlineMemory, body])
  have onlineMemory : simulatorMemoryRun lazyOnlineMachine (2 ^ 46)
      (compiledOnlineMemory memory body) oracle =
      lazyOnlineResult (compiledOnlineMemory memory body) input value oracle := by
    unfold simulatorMemoryRun simulatorStart
    simp only [zero]
    rw [online, PMF.map_comp]
    convert PMF.map_id (lazyOnlineResult (compiledOnlineMemory memory body) input value oracle) using 1
    congr 1
    funext result
    cases result <;> rfl
  rw [onlineMemory] at executed
  change (simulatorMemoryRun lazyCompiledMachine lazyCompiledMachine.secondFuel inputMemory oracle).map _ = _
  rw [executed]
  simp only [PMF.map_comp, Function.comp_def]
  congr 1
  funext result
  cases result <;> rfl

end
end Kriterion.ArgoMAC.ArithmeticSimulator
