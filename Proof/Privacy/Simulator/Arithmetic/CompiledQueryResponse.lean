import Proof.Privacy.Simulator.Arithmetic.CompiledMachineRun
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerRun
import Proof.Privacy.Simulator.Arithmetic.RespondSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- Every public branch reaches an explicit normal or cutoff halt. -/
theorem recordedPublicBranchSamples_complete (kind : PublicHandlerKind)
    (attempts count overlayCount : Nat) (memory : Memory) :
    none ∉ (recordedPublicBranchSamples kind attempts count overlayCount memory).support := by
  cases kind <;> simp [recordedPublicBranchSamples, PMF.mem_support_map_iff]

/-- Canonical decoding retains a completed branch result. -/
theorem recordedPublicHandlerSamples_complete (attempts count overlayCount : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) :
    none ∉ (recordedPublicHandlerSamples attempts count overlayCount memory request rest).support := by
  simp only [recordedPublicHandlerSamples, PMF.mem_support_map_iff]
  rintro ⟨result, member, same⟩
  cases result with
  | none => exact recordedPublicBranchSamples_complete _ _ _ _ _ member
  | some result => simp at same

/-- The protocol starts the query body with its exact canonical request and empty output. -/
noncomputable def compiledQueryMemory (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) : Memory :=
  {memory with bits := Function.update (Function.update memory.bits 0
    (GarbledCircuit.SimulatorProtocol.query request)) 3 []}

/-- The full machine retains the public source and both dispatch charges. -/
theorem compiledMachine_publicRun [BN254.FieldCertificate] (attempts count overlayCount : Nat)
    (memory : Memory) (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (overlayFits : overlayCount < 2 ^ 256)
    (counts : PublicBranchCounts (publicHandlerKind request) attempts count overlayCount
      (recordedPublicInputMemory (compiledQueryMemory memory request) request [])) :
    run (compiledMachine attempts)
      (2 + recordedPublicHandlerReserve attempts count overlayCount (compiledQueryMemory memory request) request [])
      ⟨0, {memory with bits := Function.update (Function.update memory.bits 0
        ([true, false] ++ GarbledCircuit.SimulatorProtocol.query request)) 3 []}⟩ =
      (recordedPublicHandlerSamples attempts count overlayCount (compiledQueryMemory memory request) request []).map
        (Option.map fun result =>
          (relocateConfiguration (phaseQueryLabels (offlineMachine attempts) (onlineMachine attempts)
            (recordedPublicHandler attempts)) result.1, result.2 + 2)) := by
  rw [compiledMachine_queryRun attempts _ _ (GarbledCircuit.SimulatorProtocol.query request)
    (by simp)]
  have prepared : phaseDispatchMemory
      {memory with bits := Function.update (Function.update memory.bits 0
        ([true, false] ++ GarbledCircuit.SimulatorProtocol.query request)) 3 []}
      (GarbledCircuit.SimulatorProtocol.query request) = compiledQueryMemory memory request := by
    simp [phaseDispatchMemory, compiledQueryMemory, Function.update_comm (show (0 : Fin 4) ≠ 3 by decide)]
  rw [prepared, recordedPublicHandler_run attempts count overlayCount _ request []
    (by simp [compiledQueryMemory]) attemptFits tableFits overlayFits counts]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
