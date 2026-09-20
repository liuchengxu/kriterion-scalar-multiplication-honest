import Proof.Privacy.Simulator.Arithmetic.CompiledQueryResponse
import Proof.Privacy.Simulator.Arithmetic.ParsedProgramSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
noncomputable section

/-- The protocol response preserves the actual public source and charges its dispatch. -/
theorem compiledMachine_queryResponse [BN254.FieldCertificate] (attempts count overlayCount : Nat)
    (state : State) (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256) (overlayFits : overlayCount < 2 ^ 256)
    (counts : PublicBranchCounts (publicHandlerKind request) attempts count overlayCount
      (recordedPublicInputMemory (compiledQueryMemory state.memory request) request []))
    (enough : state.spent + (2 + recordedPublicHandlerReserve attempts count overlayCount
      (compiledQueryMemory state.memory request) request []) ≤ budget (state.queries + 1)) :
    respond (compiledMachine attempts) ([true, false] ++ GarbledCircuit.SimulatorProtocol.query request)
      {state with queries := state.queries + 1} =
      (recordedPublicHandlerSamples attempts count overlayCount (compiledQueryMemory state.memory request) request []).map
        (Option.map fun result => (result.1.memory.bits 3,
          (⟨result.1.memory, state.spent + (result.2 + 2), state.queries + 1⟩ : State))) := by
  have implemented := compiledMachine_publicRun attempts count overlayCount state.memory request
    attemptFits tableFits overlayFits counts
  have complete : none ∉ ((recordedPublicHandlerSamples attempts count overlayCount
      (compiledQueryMemory state.memory request) request []).map
        (Option.map fun result =>
          (relocateConfiguration (phaseQueryLabels (offlineMachine attempts) (onlineMachine attempts)
            (recordedPublicHandler attempts)) result.1, result.2 + 2))).support := by
    rintro member
    obtain ⟨result, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    cases result with
    | none => exact recordedPublicHandlerSamples_complete attempts count overlayCount _ request [] reached
    | some result => simp at same
  have response := respond_source_optional (compiledMachine attempts)
    ([true, false] ++ GarbledCircuit.SimulatorProtocol.query request) {state with queries := state.queries + 1}
    _ _ enough complete implemented
  rw [response]
  refine (PMF.map_comp _ _ _).trans ?_
  congr 1
  funext result
  cases result <;> rfl

/-- The parsed protocol has the exact typed source, memory, and cumulative charge. -/
theorem compiledMachine_parsedResponse [BN254.FieldCertificate] (attempts count overlayCount : Nat)
    (state : State) (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256) (overlayFits : overlayCount < 2 ^ 256)
    (counts : PublicBranchCounts (publicHandlerKind request) attempts count overlayCount
      (recordedPublicInputMemory (compiledQueryMemory state.memory request) request []))
    (enough : state.spent + (2 + recordedPublicHandlerReserve attempts count overlayCount
      (compiledQueryMemory state.memory request) request []) ≤ budget (state.queries + 1)) :
    parsedResponse (compiledMachine attempts) request state =
      (recordedPublicHandlerSamples attempts count overlayCount (compiledQueryMemory state.memory request) request []).map
        (fun result => result.bind fun result => (answer request (result.1.memory.bits 3)).map fun reply =>
          (reply, (⟨result.1.memory, state.spent + (result.2 + 2), state.queries + 1⟩ : State))) := by
  unfold parsedResponse
  rw [compiledMachine_queryResponse attempts count overlayCount state request attemptFits tableFits overlayFits counts enough]
  unfold bindCutoff
  rw [PMF.bind_map]
  change PMF.bind _ _ = PMF.bind _ _
  congr 1
  funext result
  cases result <;> rfl

end
end Kriterion.ArgoMAC.ArithmeticSimulator
