import Proof.Privacy.Simulator.Arithmetic.CompiledMachineRun
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineValid
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineNull
import Proof.Privacy.Simulator.Arithmetic.RespondSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
noncomputable section

/-- The online phase receives the request body and an empty response stack. -/
def compiledOnlineMemory (memory : Memory) (body : List Bool) : Memory :=
  {memory with bits := Function.update (Function.update memory.bits 0 body) 3 []}

/-- The compiled online response preserves the full source memory and exact cumulative charge. -/
theorem compiledMachine_onlineResponse [FieldCertificate] (attempts reserve : Nat)
    (state : State) (body : List Bool)
    (source : PMF (Configuration 290305300 × Nat))
    (implemented : ClosedRun (onlineMachine attempts) 0 (compiledOnlineMemory state.memory body) reserve source)
    (enough : state.spent + (2 + reserve) ≤ budget state.queries) :
    respond (compiledMachine attempts) ([false, true] ++ body) state =
      source.map (fun result => some (result.1.memory.bits 3,
        (⟨result.1.memory, state.spent + (result.2 + 2), state.queries⟩ : State))) := by
  let inputMemory : Memory := {state.memory with bits := Function.update (Function.update state.memory.bits 0 ([false, true] ++ body)) 3 []}
  have wire : inputMemory.bits 0 = false :: true :: body := by simp [inputMemory]
  have prepared : phaseDispatchMemory inputMemory body = compiledOnlineMemory state.memory body := by
    simp [phaseDispatchMemory, inputMemory, compiledOnlineMemory,
      Function.update_comm (show (0 : Fin 4) ≠ 3 by decide)]
  have executed := compiledMachine_onlineRun attempts reserve inputMemory body wire
  have closed := implemented 0
  simp only [Nat.add_zero] at closed
  rw [prepared, closed, PMF.map_comp] at executed
  let lifted := source.map fun result =>
    (relocateConfiguration (phaseOnlineLabels (offlineMachine attempts) (onlineMachine attempts)
      (recordedPublicHandler attempts)) result.1, result.2 + 2)
  have completed : run (compiledMachine attempts) (2 + reserve) ⟨0, inputMemory⟩ = lifted.map some := by
    simpa only [lifted, PMF.map_comp, Function.comp_def, Option.map_some] using executed
  have response := respond_source (compiledMachine attempts) ([false, true] ++ body) state (2 + reserve) lifted enough completed
  rw [response]
  refine (PMF.map_comp _ _ _).trans ?_
  rfl

/-- Every complete online source sample fits its checked instruction reserve. -/
theorem compiledOnlineSource_cost [FieldCertificate] (attempts reserve : Nat) (memory : Memory)
    (source : PMF (Configuration 290305300 × Nat))
    (implemented : ClosedRun (onlineMachine attempts) 0 memory reserve source)
    (result : Configuration 290305300 × Nat) (supported : result ∈ source.support) : result.2 ≤ reserve := by
  have executed := implemented 0
  simp only [Nat.add_zero] at executed
  have member : some result ∈ (run (onlineMachine attempts) reserve ⟨0, memory⟩).support := by
    rw [executed]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, supported, rfl⟩
  exact run_cost (onlineMachine attempts) reserve ⟨0, memory⟩ result.1 result.2 member

/-- The valid protocol response includes every actual online phase and its source charge. -/
theorem compiledMachine_onlineValidResponse [FieldCertificate] [GroupCertificate]
    (attempts limit : Nat) (state : State) (input : AffineInput) (output : Point)
    (family : SparseOracleFamily) (key : BaseField) (suffix : List Bool)
    (attemptFits : attempts < 2 ^ 256)
    (ready : OnlineSampledReady attempts limit
      (onlineTagMemory (onlineCurveMemory
        (compiledOnlineMemory state.memory (affine input ++ GarbledCircuit.SimulatorProtocol.output (some output) ++ suffix))
        input (some output) suffix)) output family key suffix)
    (enough : state.spent + (2 + (onlinePrefixCost (some output) +
      (3 + (1 + (onlineSamplingBudget attempts + onlineSelectedReserve attempts limit family))))) ≤ budget state.queries) :
    respond (compiledMachine attempts)
      ([false, true] ++ (affine input ++ GarbledCircuit.SimulatorProtocol.output (some output) ++ suffix)) state =
      (onlineValidSamples attempts
        (compiledOnlineMemory state.memory (affine input ++ GarbledCircuit.SimulatorProtocol.output (some output) ++ suffix))
        input output family key suffix).map (fun result => some (result.1.memory.bits 3,
          (⟨result.1.memory, state.spent + (result.2 + 2), state.queries⟩ : State))) := by
  apply compiledMachine_onlineResponse attempts _ state _ _ _ enough
  exact onlineMachine_valid attempts limit _ input output family key suffix
    (by simp [compiledOnlineMemory]) attemptFits ready

/-- The absent-output source includes the common prefix and all curve gates. -/
def compiledOnlineNullSamples [FieldCertificate] (attempts : Nat) (memory : Memory)
    (input : AffineInput) (suffix : List Bool) : PMF (Configuration 290305300 × Nat) :=
  ((((gateLoopSamples curveGatePlan attempts 1270 0
    (onlineNullGateInitial (onlineCurveMemory memory input none suffix))).map onlineNullGateResult).map
      fun result => (result.1, result.2 + 6)).map
        fun result => (result.1, result.2 + onlinePrefixCost none))

/-- The absent-output protocol response retains its exact curve source and cumulative charge. -/
theorem compiledMachine_onlineNullResponse [FieldCertificate]
    (attempts limit : Nat) (state : State) (input : AffineInput) (suffix : List Bool)
    (attemptFits : attempts < 2 ^ 256)
    (ready : GateLoopReady curveGatePlan attempts limit 1270 0
      (onlineNullGateInitial (onlineCurveMemory
        (compiledOnlineMemory state.memory (affine input ++ GarbledCircuit.SimulatorProtocol.output none ++ suffix))
        input none suffix)))
    (kept : ∀ result ∈ (gateLoopSamples curveGatePlan attempts 1270 0
      (onlineNullGateInitial (onlineCurveMemory
        (compiledOnlineMemory state.memory (affine input ++ GarbledCircuit.SimulatorProtocol.output none ++ suffix))
        input none suffix))).support,
      result.1 = true → result.2.1.ram (BitVec.ofNat 256 (onlineInputBase + 2)) = 0)
    (enough : state.spent + (2 + (onlinePrefixCost none +
      (6 + (gateDriverRunBudget attempts limit * 1270 + 200666)))) ≤ budget state.queries) :
    respond (compiledMachine attempts)
      ([false, true] ++ (affine input ++ GarbledCircuit.SimulatorProtocol.output none ++ suffix)) state =
      (compiledOnlineNullSamples attempts
        (compiledOnlineMemory state.memory (affine input ++ GarbledCircuit.SimulatorProtocol.output none ++ suffix))
        input suffix).map (fun result => some (result.1.memory.bits 3,
          (⟨result.1.memory, state.spent + (result.2 + 2), state.queries⟩ : State))) := by
  apply compiledMachine_onlineResponse attempts _ state _ _ _ enough
  exact onlineMachine_null attempts limit _ input suffix (by simp [compiledOnlineMemory]) attemptFits ready kept

end
end Kriterion.ArgoMAC.ArithmeticSimulator
