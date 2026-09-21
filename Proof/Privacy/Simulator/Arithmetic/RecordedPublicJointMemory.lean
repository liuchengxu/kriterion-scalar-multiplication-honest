import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerFamily
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerHistory
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicJointSupport
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicJointReady

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine

/-- Every successful joint public query preserves its exact family and fixed-query history in RAM. -/
theorem recordedPublicJoint_memory [BN254.FieldCertificate]
    (attempts : Nat) (memory : Memory) (state : SharedOracleSource) (request : SharedQuery) (rest : List Bool)
    (represented : OracleFamilyMemory memory.ram state.family) (capacity : OracleFamilyFits state.family)
    (history : SharedHistoryMemory memory.ram state.metadata)
    (room : ∀ oracle, 2 * ((state.family.permutations oracle).base.used + 1) + 256 < 2 ^ 110)
    (hashRoom : 2 * (state.family.hash.length + 1) + 256 < 2 ^ 110)
    (historyRoom : ∀ current, 257 + 2 * (recordHistoryPairs state.metadata.fixedTranscript current).length < 2 ^ 110)
    (empty : memory.bits 3 = []) (result : Configuration 1810 × Nat)
    (reply : SharedAnswer request) (next : SharedOracleSource)
    (supported : (some result, some (reply, next)) ∈ (recordedPublicJoint attempts memory state request rest).support) :
    OracleFamilyMemory result.1.memory.ram next.family ∧ OracleFamilyFits next.family ∧
      SharedHistoryMemory result.1.memory.ram next.metadata := by
  obtain ⟨member, answered, recovered⟩ := recordedPublicJoint_support attempts memory state request rest result reply next supported
  subst next
  have stable := recordedPublicJoint_ready attempts memory state request rest represented capacity history
    (fun oracle => by have := room oracle; omega) historyRoom
  have family := recordedPublicHandlerSamples_family attempts memory state request rest represented capacity history
    room hashRoom historyRoom empty stable result reply member answered
  have recorded := recordedPublicHandlerSamples_history attempts memory state request rest represented capacity history
    room hashRoom historyRoom empty stable result reply member answered
  exact ⟨family.1, family.2, recorded⟩

/-- Each successful source reply has an actual machine result with the same complete RAM state. -/
theorem recordedPublicJoint_successMemory [BN254.FieldCertificate]
    (attempts : Nat) (memory : Memory) (state : SharedOracleSource) (request : SharedQuery) (rest : List Bool)
    (represented : OracleFamilyMemory memory.ram state.family) (capacity : OracleFamilyFits state.family)
    (history : SharedHistoryMemory memory.ram state.metadata)
    (room : ∀ oracle, 2 * ((state.family.permutations oracle).base.used + 1) + 256 < 2 ^ 110)
    (hashRoom : 2 * (state.family.hash.length + 1) + 256 < 2 ^ 110)
    (historyRoom : ∀ current, 257 + 2 * (recordHistoryPairs state.metadata.fixedTranscript current).length < 2 ^ 110)
    (empty : memory.bits 3 = []) (machine : Option (Configuration 1810 × Nat))
    (reply : SharedAnswer request) (next : SharedOracleSource)
    (supported : (machine, some (reply, next)) ∈ (recordedPublicJoint attempts memory state request rest).support) :
    ∃ result, machine = some result ∧ OracleFamilyMemory result.1.memory.ram next.family ∧
      OracleFamilyFits next.family ∧ SharedHistoryMemory result.1.memory.ram next.metadata := by
  obtain ⟨result, rfl⟩ := recordedPublicJoint_sourceSuccess attempts memory state request rest machine reply next supported
  exact ⟨result, rfl, recordedPublicJoint_memory attempts memory state request rest represented capacity history
    room hashRoom historyRoom empty result reply next supported⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
