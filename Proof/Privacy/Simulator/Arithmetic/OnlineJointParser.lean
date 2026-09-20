import Proof.Privacy.Simulator.Arithmetic.OnlineJoint
import Proof.Privacy.Simulator.Arithmetic.SharedParsedGame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
open GarbledCircuit.SimulatorProtocol
noncomputable section
attribute [local irreducible] words run respond

/-- The parser preserves the joint labels, accepted memory, and exact cumulative charge. -/
theorem onlineJoint_parsed [FieldCertificate] (state : State)
    (joint : PMF (Option OnlineJointMemoryResult)) (actual : PMF (Configuration 290305300 × Nat))
    (machine : joint.map (Option.map fun result => result.2.1) =
      actual.map (fun result => if result.1.pc = 290305298 then some (result.1.memory, result.2) else none))
    (labels : ∀ result, some result ∈ joint.support →
      words 128 508 (result.2.1.1.bits 3) = some (Lamport.selectedLabels result.1.inputMac))
    (failure : ∀ result ∈ actual.support, result.1.pc ≠ 290305298 →
      words 128 508 (result.1.memory.bits 3) = none) :
    joint.map (Option.map fun result =>
      (Lamport.selectedLabels result.1.inputMac,
        (⟨result.2.1.1, state.spent + (result.2.1.2 + 2), state.queries⟩ : State))) =
      actual.map (fun result => (words 128 508 (result.1.memory.bits 3)).map fun selected =>
        (selected, (⟨result.1.memory, state.spent + (result.2 + 2), state.queries⟩ : State))) := by
  let parse (result : Option (Memory × Nat)) : Option (GarbledCircuit.LamportSignature × State) :=
    result.bind fun result => (words 128 508 (result.1.bits 3)).map fun selected =>
      (selected, (⟨result.1, state.spent + (result.2 + 2), state.queries⟩ : State))
  have decoded : joint.map (Option.map fun result =>
      (Lamport.selectedLabels result.1.inputMac,
        (⟨result.2.1.1, state.spent + (result.2.1.2 + 2), state.queries⟩ : State))) =
      (joint.map (Option.map fun result => result.2.1)).map parse := by
    rw [PMF.map_comp]
    change joint.bind _ = joint.bind _
    apply ThreePhase.bind_eq_on_support
    intro result member
    cases result with
    | none => rfl
    | some result => simp only [Function.comp_def, Option.map_some, parse, Option.bind_some,
        labels result member, Option.map_some]
  rw [decoded, machine, PMF.map_comp]
  change actual.bind _ = actual.bind _
  apply ThreePhase.bind_eq_on_support
  intro result member
  by_cases normal : result.1.pc = 290305298
  · simp only [Function.comp_def, if_pos normal, parse, Option.bind_some]
  · simp only [Function.comp_def, if_neg normal, parse, Option.bind_none, failure result member normal,
      Option.map_none]

/-- The complete actual response and joint memory source have the same parsed online marginal. -/
theorem compiledOnlineJoint_parsed [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (coin : SimulatorSampling.OfflineCoin) (input : AffineInput) (output : Option Point)
    (state : State) (source : SharedOracleSource) (actual : PMF (Configuration 290305300 × Nat))
    (response : respond (compiledMachine attempts) ([false, true] ++ affine input ++ GarbledCircuit.SimulatorProtocol.output output) state =
      actual.map (fun result => some (result.1.memory.bits 3,
        (⟨result.1.memory, state.spent + (result.2 + 2), state.queries⟩ : State))))
    (machine : (onlineMemoryJoint attempts coin input output
      (compiledOnlineMemory state.memory (affine input ++ GarbledCircuit.SimulatorProtocol.output output)) source).map
        (Option.map fun result => result.2.1) =
      actual.map (fun result => if result.1.pc = 290305298 then some (result.1.memory, result.2) else none))
    (labels : ∀ result, some result ∈
      (onlineMemoryJoint attempts coin input output
        (compiledOnlineMemory state.memory (affine input ++ GarbledCircuit.SimulatorProtocol.output output)) source).support →
      words 128 508 (result.2.1.1.bits 3) = some (Lamport.selectedLabels result.1.inputMac))
    (failure : ∀ result ∈ actual.support, result.1.pc ≠ 290305298 →
      words 128 508 (result.1.memory.bits 3) = none) :
    (compiledOnlineJoint attempts coin input output state source).map
      (Option.map fun result => (Lamport.selectedLabels result.1.inputMac, result.2.1)) =
      sharedParsedOnline (compiledMachine attempts) state input output := by
  rw [sharedParsedOnline, response]
  simpa only [compiledOnlineJoint, PMF.map_comp, Option.map_map, Function.comp_def,
    Option.bind_some] using onlineJoint_parsed state _ actual machine labels failure

end
end Kriterion.ArgoMAC.ArithmeticSimulator
