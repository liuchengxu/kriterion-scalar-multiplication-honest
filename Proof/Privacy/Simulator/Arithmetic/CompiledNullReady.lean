import Proof.Privacy.Simulator.Arithmetic.OnlineNullJointMemory
import Proof.Privacy.Simulator.Arithmetic.CompiledOnlineReady

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
noncomputable section
attribute [local irreducible] onlineMemoryJoint compiledOnlineJoint compiledOnlineNullSamples

private theorem nullRoom (used : Nat) (small : used < 2 ^ 101) :
    256 + 2 * (used + 3811) < 2 ^ 110 := by
  have capacity := oracleTable_capacity used small
  exact lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left 2
    (Nat.add_le_add_left (by decide : 3811 ≤ 836423) used)) 256)
      (by simpa only [Nat.add_comm 256] using capacity)

/-- The complete absent-output phase supplies the decision phase's concrete invariant. -/
theorem compiledNullJoint_ready [FieldCertificate] [GroupCertificate]
    (coin : SimulatorSampling.OfflineCoin) (input : AffineInput)
    (used setupSpent : Nat) (state : State) (source : SharedOracleSource)
    (setup : setupSpent ≤ 2 ^ 30 + 605084290688 + 2)
    (initial : CompiledPublicReady 256 0 0 0 setupSpent used state source)
    (stored : WordsAt state.memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (small : used < 2 ^ 101)
    (labels : Garbling.Labels) (final : State) (next : SharedOracleSource)
    (member : some (labels, final, next) ∈ (compiledOnlineJoint 256 coin input none state source).support) :
    CompiledDecisionReady used final next := by
  let memory := compiledOnlineMemory state.memory
    (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output none)
  have represented : SharedSourceMemory memory source used := by
    simpa only [Nat.zero_add] using initial.memory.ramEq (updated := memory) rfl
  have words : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin) := stored
  have room := nullRoom used small
  have shortRoom : 256 + 2 * (used + 3810) < 2 ^ 110 :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left 2
      (Nat.add_le_add_left (by decide : 3810 ≤ 3811) used)) 256) room
  have ready := onlineNull_ready 256 used memory input none [] coin source words represented shortRoom
  apply compiledOnlineJoint_ready coin input none used setupSpent _ state source setup initial
    (compiledOnlineNullSamples 256 memory input [])
  · exact onlineNullMemoryJoint_run 256 used memory input coin source words represented room (by decide) (by
      simp only [memory, compiledOnlineMemory, Function.update_of_ne (by decide : (0 : Fin 4) ≠ 3), Function.update_self])
  · exact onlineMachine_nullPrefixCost used (used + 3810) source.family (by omega)
      (by simpa only [Nat.zero_add] using initial.hash)
  · simp only [onlineMemoryJoint]
    change (onlineNullMemoryJoint 256 (sharedOfflineFrame coin) input memory source).map _ = _
    exact onlineNullMemoryJoint_machine 256 used (sharedOfflineFrame coin) input memory source ready shortRoom (by decide)
  · simp only [onlineMemoryJoint]
    change (onlineNullMemoryJoint 256 (sharedOfflineFrame coin) input memory source).map _ = _
    exact onlineNullMemoryJoint_source 256 used (sharedOfflineFrame coin) input memory source ready shortRoom
  · intro result supported
    simp only [onlineMemoryJoint] at supported
    change some result ∈ (onlineNullMemoryJoint 256 (sharedOfflineFrame coin) input memory source).support at supported
    have retained := (onlineNullMemoryJoint_memory 256 used memory input coin source words represented shortRoom result supported).1
    exact ⟨retained.family, retained.capacity, retained.history⟩
  · exact member

end
end Kriterion.ArgoMAC.ArithmeticSimulator
