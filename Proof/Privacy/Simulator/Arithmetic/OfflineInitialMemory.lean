import Proof.Privacy.Simulator.Arithmetic.OfflineSourceJoint
import Proof.Privacy.Simulator.Arithmetic.OfflineMachineRun
import Proof.Privacy.Simulator.Arithmetic.GateSlotInvariant
import Proof.Privacy.Simulator.Arithmetic.OracleFamilyInitial

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section
attribute [local irreducible] publicWireProgram offlinePlan samplerBatchMemory offlineSchedule

/-- The serializer retains every private word and public header. -/
theorem publicWireProgram_ram (memory : Memory) :
    (executeLinear publicWireProgram memory).ram = memory.ram := by
  rw [publicWireProgram_eq]
  exact (wireSegments_preserves publicWire memory).1

/-- The private source writer does not change a public oracle cell. -/
theorem offlineStored_public (ram : Word → Word) (coin : Security.SimulatorSampling.OfflineCoin)
    (oracle : Fin 15749) (table : Fin 4) (offset : Nat) (fits : offset < 2 ^ 110) :
    storeDrawWords (BitVec.ofNat 256 privateBase) 0 ram (offlineSchedule.words coin)
      (oracleAddress oracle table offset) = ram (oracleAddress oracle table offset) := by
  have bounds := oracleCell_bounds oracle table offset fits
  have difference : privateBase ≤ oracleCell oracle table offset := by
    unfold privateBase
    omega
  have outside : (offlineSchedule.words coin).length ≤ oracleCell oracle table offset - privateBase := by
    rw [offlineSchedule.wordsLength]
    unfold privateBase
    omega
  have queryFits : oracleCell oracle table offset - privateBase < 2 ^ 256 := by omega
  have address : BitVec.ofNat 256 privateBase +
      BitVec.ofNat 256 (oracleCell oracle table offset - privateBase) = oracleAddress oracle table offset := by
    rw [← BitVec.ofNat_add, Nat.add_sub_of_le difference]
    rfl
  have stored := storeDrawWords_outside (BitVec.ofNat 256 privateBase) 0 ram (offlineSchedule.words coin)
    (oracleCell oracle table offset - privateBase) (by rw [offlineSchedule.wordsLength]; decide)
    queryFits (Or.inr (by simpa only [Nat.zero_add] using outside))
  simpa only [address] using stored

/-- Every sampled setup result retains the initial public RAM cells. -/
theorem offlineSample_public [BN254.FieldCertificate] (attempts : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (samplerBatchMemory offlinePlan attempts 838208 0 (offlineInitialMemory base)).support)
    (oracle : Fin 15749) (table : Fin 4) (offset : Nat) (fits : offset < 2 ^ 110) :
    (executeLinear publicWireProgram final).ram (oracleAddress oracle table offset) =
      base.ram (oracleAddress oracle table offset) := by
  rw [publicWireProgram_ram, offlineMemoryCoin_memory attempts (offlineInitialMemory base) final cost supported]
  have pointer : (offlineInitialMemory base).registers 10 = BitVec.ofNat 256 privateBase := by
    simp only [offlineInitialMemory, Function.update_of_ne (by decide : (10 : Register) ≠ 11), Function.update_self]
  rw [pointer]
  exact offlineStored_public base.ram _ oracle table offset fits

/-- Zero public headers represent the initial shared source and its empty history. -/
theorem initialSharedOracleSource_memory (memory : Memory) (metadata : Metadata)
    (empty : metadata.fixedTranscript = [])
    (zero : ∀ oracle table, memory.ram (oracleAddress oracle table 0) = 0) :
    SharedSourceMemory memory (initialSharedOracleSource metadata) 0 := by
  refine ⟨emptyOracleFamily_memory memory.ram zero, emptyOracleFamily_fits, ?_, ?_⟩
  · intro index
    change HistoryMemory memory.ram _ (recordHistoryPairs metadata.fixedTranscript index)
    rw [empty]
    exact HistoryMemory.empty memory.ram _ (zero _ 3)
  · constructor
    · intro index
      exact Nat.le_refl 0
    · constructor
      · intro index
        exact Nat.le_refl 0
      · intro index
        change (recordHistoryPairs metadata.fixedTranscript index).length ≤ 0
        simp only [empty, recordHistoryPairs, List.filter_nil, List.reverse_nil, List.map_nil, List.length_nil, le_refl]

/-- The sampled setup memory represents the empty oracle source after serialization. -/
theorem offlineSample_initialSource [BN254.FieldCertificate] (attempts : Nat) (base final : Memory) (cost : Nat)
    (zero : ∀ oracle table, base.ram (oracleAddress oracle table 0) = 0)
    (supported : (final, cost) ∈ (samplerBatchMemory offlinePlan attempts 838208 0 (offlineInitialMemory base)).support)
    (metadata : Metadata) (empty : metadata.fixedTranscript = []) :
    SharedSourceMemory (executeLinear publicWireProgram final) (initialSharedOracleSource metadata) 0 := by
  apply initialSharedOracleSource_memory _ metadata empty
  intro oracle table
  exact (offlineSample_public attempts base final cost supported oracle table 0 (by decide)).trans (zero oracle table)

/-- Every setup joint result retains all typed private words and the empty oracle source. -/
theorem offlineSourceJoint_initialMemory [BN254.FieldCertificate] (attempts : Nat) (base final : Memory)
    (cost : Nat) (coin : Security.SimulatorSampling.OfflineCoin)
    (zero : ∀ oracle table, base.ram (oracleAddress oracle table 0) = 0)
    (supported : ((final, cost), coin) ∈ (offlineSourceJoint attempts (offlineInitialMemory base)).support)
    (metadata : Metadata) (empty : metadata.fixedTranscript = []) :
    SharedSourceMemory (executeLinear publicWireProgram final) (initialSharedOracleSource metadata) 0 ∧
      WordsAt (executeLinear publicWireProgram final).ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin) ∧
      (initialSharedOracleSource metadata).family.hash = [] := by
  have member : (final, cost) ∈ (samplerBatchMemory offlinePlan attempts 838208 0 (offlineInitialMemory base)).support := by
    rw [← offlineSourceJoint_machine]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨((final, cost), coin), supported, rfl⟩
  refine ⟨offlineSample_initialSource attempts base final cost zero member metadata empty, ?_, rfl⟩
  rw [publicWireProgram_ram]
  have words := offlineSourceJoint_words attempts (offlineInitialMemory base) final cost coin supported
  simpa only [offlineInitialMemory, Function.update_of_ne (by decide : (10 : Register) ≠ 11),
    Function.update_self] using words

end
end Kriterion.ArgoMAC.ArithmeticSimulator
