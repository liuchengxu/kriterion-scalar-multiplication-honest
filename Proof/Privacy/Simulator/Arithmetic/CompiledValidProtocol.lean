import Proof.Privacy.Simulator.Arithmetic.OnlineActualReady
import Proof.Privacy.Simulator.Arithmetic.OnlineValidConcrete
import Proof.Privacy.Simulator.Arithmetic.OnlineValidJointMemory
import Proof.Privacy.Simulator.Arithmetic.CompiledOnlineReady
import Proof.Privacy.Simulator.Arithmetic.OnlineJointParser
import Proof.Privacy.Simulator.Arithmetic.OnlineAbortBits

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
noncomputable section
set_option maxRecDepth 2048
attribute [local irreducible] compiledMachine onlineMemoryJoint onlineValidSamples

/-- The complete compiled valid phase has the exact finite online source marginal. -/
theorem compiledValidJoint_source [FieldCertificate] [GroupCertificate]
    (attempts limit : Nat) (coin : SimulatorSampling.OfflineCoin) (input : AffineInput) (output : Point)
    (state : State) (source : SharedOracleSource)
    (stored : WordsAt state.memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (represented : SharedSourceMemory state.memory source limit)
    (room : 256 + 2 * (limit + 836422) < 2 ^ 110)
    (hashRoom : 2 * (source.family.hash.length + 1) + 256 < 2 ^ 110) :
    (compiledOnlineJoint attempts coin input (some output) state source).map
      (Option.map fun result => (result.1, result.2.2)) =
      runSampledCutoff (sharedSourceCutoff attempts)
        (sharedOnlineTotalProgram attempts (sharedOfflineFrame coin) input (some output)) source := by
  let memory := compiledOnlineMemory state.memory
    (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output (some output))
  simpa only [compiledOnlineJoint, onlineMemoryJoint, PMF.map_comp, Function.comp_def, Option.map_map]
    using onlineValidMemoryJoint_concreteSource attempts limit memory input output coin source stored
      (represented.ramEq rfl) room hashRoom

/-- The checked valid run closes both protocol marginals and the final decision invariant. -/
theorem compiledValidJoint_coupling_of_run [FieldCertificate] [GroupCertificate]
    (coin : SimulatorSampling.OfflineCoin) (input : AffineInput) (output : Point)
    (used setupSpent reserve : Nat) (state : State) (source : SharedOracleSource)
    (setup : setupSpent ≤ 2 ^ 30 + 605084290688 + 2)
    (initial : CompiledPublicReady 256 0 0 0 setupSpent used state source)
    (stored : WordsAt state.memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (room : 256 + 2 * (used + 836423) < 2 ^ 110)
    (hashRoom : 2 * (source.family.hash.length + 1) + 256 < 2 ^ 110)
    (executed : ClosedRun (onlineMachine 256) 0
      (compiledOnlineMemory state.memory (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output (some output)))
      reserve (onlineValidSamples 256
        (compiledOnlineMemory state.memory (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output (some output)))
        input output source.family coin.2.2 []))
    (charged : reserve ≤ 2153421270 * 256 + 46833536 * (used + 836423) + 6 * used + 235015545) :
    ((compiledOnlineJoint 256 coin input (some output) state source).map
      (Option.map fun result => (Lamport.selectedLabels result.1.inputMac, result.2.1)) =
      sharedParsedOnline (compiledMachine 256) state input (some output)) ∧
    ((compiledOnlineJoint 256 coin input (some output) state source).map (Option.map fun result => (result.1, result.2.2)) =
      runSampledCutoff (sharedSourceCutoff 256) (sharedOnlineTotalProgram 256 (sharedOfflineFrame coin) input (some output)) source) ∧
    ∀ labels final, some (labels, final) ∈ (compiledOnlineJoint 256 coin input (some output) state source).support →
      CompiledDecisionReady used final.1 final.2 := by
  let memory := compiledOnlineMemory state.memory
    (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output (some output))
  let actual := onlineValidSamples 256 memory input output source.family coin.2.2 []
  have represented : SharedSourceMemory memory source used := by
    simpa only [Nat.zero_add] using initial.memory.ramEq (updated := memory) rfl
  have shortRoom : 256 + 2 * (used + 836422) < 2 ^ 110 :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left 2
      (Nat.add_le_add_left (by decide : 836422 ≤ 836423) used)) 256) room
  have machineLaw := onlineValidMemoryJoint_concreteMachine 256 used memory input output coin source
    stored represented shortRoom hashRoom (by decide)
  have sourceLaw := onlineValidMemoryJoint_concreteSource 256 used memory input output coin source
    stored represented shortRoom hashRoom
  have empty : memory.bits 3 = [] := by simp only [memory, compiledOnlineMemory, Function.update_self]
  have retained := onlineValidMemoryJoint_memory 256 used memory input output coin source stored represented
    room hashRoom (by decide) empty
  have enough : state.spent + (2 + reserve) ≤ budget state.queries := by
    have bound := compiledOnlineCost_budget used setupSpent reserve setup charged
    rw [initial.queries]
    simpa only [Nat.zero_add, Nat.add_comm 2] using (Nat.add_le_add_right initial.spent _).trans bound
  refine ⟨?_, compiledValidJoint_source 256 used coin input output state source stored
    (by simpa only [Nat.zero_add] using initial.memory) shortRoom hashRoom, ?_⟩
  · apply compiledOnlineJoint_parsed 256 coin input (some output) state source actual
    · exact compiledMachine_onlineResponse 256 reserve state _ actual executed enough
    · simpa only [onlineMemoryJoint] using machineLaw
    · intro result supported
      simp only [onlineMemoryJoint] at supported
      exact (retained result supported).2
    · exact onlineValidSamples_abortParser 256 memory input output source.family coin.2.2 [] empty
  · intro labels final supported
    apply compiledOnlineJoint_ready coin input (some output) used setupSpent reserve state source setup initial
      actual executed charged
    · simpa only [onlineMemoryJoint] using machineLaw
    · simpa only [onlineMemoryJoint] using sourceLaw
    · intro result member
      simp only [onlineMemoryJoint] at member
      have resultMemory := (retained result member).1
      exact ⟨resultMemory.family, resultMemory.capacity, resultMemory.history⟩
    · exact supported

/-- The complete concrete valid phase meets the revised online coupling interface. -/
theorem compiledValidJoint_coupling [FieldCertificate] [GroupCertificate]
    (coin : SimulatorSampling.OfflineCoin) (input : AffineInput) (output : Point)
    (used setupSpent : Nat) (state : State) (source : SharedOracleSource)
    (small : used < 2 ^ 101) (setup : setupSpent ≤ 2 ^ 30 + 605084290688 + 2)
    (initial : CompiledPublicReady 256 0 0 0 setupSpent used state source)
    (stored : WordsAt state.memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin)) :
    ((compiledOnlineJoint 256 coin input (some output) state source).map
      (Option.map fun result => (Lamport.selectedLabels result.1.inputMac, result.2.1)) =
      sharedParsedOnline (compiledMachine 256) state input (some output)) ∧
    ((compiledOnlineJoint 256 coin input (some output) state source).map (Option.map fun result => (result.1, result.2.2)) =
      runSampledCutoff (sharedSourceCutoff 256) (sharedOnlineTotalProgram 256 (sharedOfflineFrame coin) input (some output)) source) ∧
    ∀ labels final, some (labels, final) ∈ (compiledOnlineJoint 256 coin input (some output) state source).support →
      CompiledDecisionReady used final.1 final.2 := by
  let memory := compiledOnlineMemory state.memory
    (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output (some output))
  have represented : SharedSourceMemory memory source used := by
    simpa only [Nat.zero_add] using initial.memory.ramEq (updated := memory) rfl
  have hashBound : source.family.hash.length ≤ used := by simpa only [Nat.zero_add] using initial.hash
  have capacity := oracleTable_capacity used small
  have room : 256 + 2 * (used + 836423) < 2 ^ 110 := by simpa only [Nat.add_comm 256] using capacity
  have hashRoom : 2 * (source.family.hash.length + 1) + 256 < 2 ^ 110 := by
    apply lt_of_le_of_lt _ room
    rw [Nat.add_comm 256]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2
      (Nat.add_le_add hashBound (by decide : 1 ≤ 836423))) 256
  apply compiledValidJoint_coupling_of_run coin input output used setupSpent _ state source setup initial stored room hashRoom
  · exact onlineValid_actualRun 256 used memory input output coin source stored represented hashBound small (by decide)
      (by simp only [memory, compiledOnlineMemory, Function.update_of_ne (by decide : (0 : Fin 4) ≠ 3), Function.update_self])
  · exact onlineMachine_validPrefixCost used (used + 836423) source.family output (Nat.le_refl _) hashBound

end
end Kriterion.ArgoMAC.ArithmeticSimulator
