import Proof.Privacy.Simulator.Arithmetic.CompiledNullReady
import Proof.Privacy.Simulator.Arithmetic.OnlineJointParser
import Proof.Privacy.Simulator.Arithmetic.OnlineNullParser
import Proof.Privacy.Simulator.Arithmetic.OnlinePrefixBits

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
noncomputable section
attribute [local irreducible] compiledMachine compiledOnlineNullSamples onlineMemoryJoint

/-- The compiled absent-output phase has the exact complete finite source marginal. -/
theorem compiledNullJoint_source [FieldCertificate] [GroupCertificate]
    (attempts limit : Nat) (coin : SimulatorSampling.OfflineCoin) (input : AffineInput)
    (state : State) (source : SharedOracleSource)
    (stored : WordsAt state.memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (represented : SharedSourceMemory state.memory source limit)
    (room : 256 + 2 * (limit + 3810) < 2 ^ 110) :
    (compiledOnlineJoint attempts coin input none state source).map
      (Option.map fun result => (result.1, result.2.2)) =
      runSampledCutoff (sharedSourceCutoff attempts)
        (sharedOnlineTotalProgram attempts (sharedOfflineFrame coin) input none) source := by
  let memory := compiledOnlineMemory state.memory
    (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output none)
  have ready := onlineNull_ready attempts limit memory input none [] coin source stored (represented.ramEq rfl) room
  simpa only [compiledOnlineJoint, onlineMemoryJoint, PMF.map_comp, Function.comp_def, Option.map_map]
    using onlineNullMemoryJoint_source attempts limit (sharedOfflineFrame coin) input memory source ready room

/-- The compiled absent-output response uses its proved reserve and exact cumulative charge. -/
theorem compiledNullJoint_response [FieldCertificate] (coin : SimulatorSampling.OfflineCoin) (input : AffineInput)
    (used setupSpent : Nat) (state : State) (source : SharedOracleSource)
    (setup : setupSpent ≤ 2 ^ 30 + 605084290688 + 2)
    (initial : CompiledPublicReady 256 0 0 0 setupSpent used state source)
    (stored : WordsAt state.memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (room : 256 + 2 * (used + 3811) < 2 ^ 110) :
    respond (compiledMachine 256)
      ([false, true] ++ (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output none)) state =
      (compiledOnlineNullSamples 256 (compiledOnlineMemory state.memory
        (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output none)) input []).map
        (fun result => some (result.1.memory.bits 3,
          (⟨result.1.memory, state.spent + (result.2 + 2), state.queries⟩ : State))) := by
  let memory := compiledOnlineMemory state.memory
    (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output none)
  have represented : SharedSourceMemory memory source used := by
    simpa only [Nat.zero_add] using initial.memory.ramEq (updated := memory) rfl
  have runLaw := onlineNullMemoryJoint_run 256 used memory input coin source stored represented room (by decide)
    (by simp only [memory, compiledOnlineMemory, Function.update_of_ne (by decide : (0 : Fin 4) ≠ 3), Function.update_self])
  have cost := onlineMachine_nullPrefixCost used (used + 3810) source.family (by omega)
    (by simpa only [Nat.zero_add] using initial.hash)
  have budgetLaw := compiledOnlineCost_budget used setupSpent _ setup cost
  have enough : state.spent + (2 + (onlinePrefixCost none +
      (6 + (gateDriverRunBudget 256 (used + 3810) * 1270 + 200666)))) ≤ budget state.queries := by
    rw [initial.queries]
    simpa only [Nat.zero_add, Nat.add_comm 2] using
      (Nat.add_le_add_right initial.spent _).trans budgetLaw
  exact compiledMachine_onlineResponse 256 _ state _ _ runLaw enough

/-- The absent-output phase meets both protocol marginals and the decision invariant. -/
theorem compiledNullJoint_coupling [FieldCertificate] [GroupCertificate]
    (coin : SimulatorSampling.OfflineCoin) (input : AffineInput)
    (used setupSpent : Nat) (state : State) (source : SharedOracleSource)
    (small : used < 2 ^ 101) (setup : setupSpent ≤ 2 ^ 30 + 605084290688 + 2)
    (initial : CompiledPublicReady 256 0 0 0 setupSpent used state source)
    (stored : WordsAt state.memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin)) :
    ((compiledOnlineJoint 256 coin input none state source).map
      (Option.map fun result => (Lamport.selectedLabels result.1.inputMac, result.2.1)) =
      sharedParsedOnline (compiledMachine 256) state input none) ∧
    ((compiledOnlineJoint 256 coin input none state source).map (Option.map fun result => (result.1, result.2.2)) =
      runSampledCutoff (sharedSourceCutoff 256) (sharedOnlineTotalProgram 256 (sharedOfflineFrame coin) input none) source) ∧
    ∀ labels final, some (labels, final) ∈ (compiledOnlineJoint 256 coin input none state source).support →
      CompiledDecisionReady used final.1 final.2 := by
  let memory := compiledOnlineMemory state.memory
    (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output none)
  have represented : SharedSourceMemory state.memory source used := by
    simpa only [Nat.zero_add] using initial.memory
  have capacity := oracleTable_capacity used small
  have room : 256 + 2 * (used + 3811) < 2 ^ 110 :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left 2
      (Nat.add_le_add_left (by decide : 3811 ≤ 836423) used)) 256)
      (by simpa only [Nat.add_comm 256] using capacity)
  have shortRoom : 256 + 2 * (used + 3810) < 2 ^ 110 :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left 2
      (Nat.add_le_add_left (by decide : 3810 ≤ 3811) used)) 256) room
  have ready := onlineNull_ready 256 used memory input none [] coin source stored (represented.ramEq rfl) shortRoom
  have empty : (onlineNullGateInitial (onlineCurveMemory memory input none [])).bits 3 = [] := by
    rw [onlineNullGateInitial_bits, onlineCurveMemory_bits, Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0)]
    rfl
  refine ⟨?_, compiledNullJoint_source 256 used coin input state source stored represented shortRoom, ?_⟩
  · apply compiledOnlineJoint_parsed 256 coin input none state source
      (compiledOnlineNullSamples 256 memory input [])
    · simpa only [List.append_assoc] using compiledNullJoint_response coin input used setupSpent state source setup initial stored room
    · simp only [onlineMemoryJoint]
      exact onlineNullMemoryJoint_machine 256 used (sharedOfflineFrame coin) input memory source ready shortRoom (by decide)
    · intro result supported
      simp only [onlineMemoryJoint] at supported
      exact onlineNullMemoryJoint_keyProtocol 256 used memory input coin source stored (represented.ramEq rfl)
        shortRoom (by decide) empty result supported
    · exact compiledOnlineNullSamples_failure 256 memory input empty
  · intro labels final supported
    exact compiledNullJoint_ready coin input used setupSpent state source setup initial stored small labels final.1 final.2 supported

end
end Kriterion.ArgoMAC.ArithmeticSimulator
