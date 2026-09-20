import Proof.Privacy.Simulator.Arithmetic.CompiledSetupProtocol
import Proof.Privacy.Simulator.Arithmetic.OfflineInitialMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security
noncomputable section
attribute [local irreducible] publicWireProgram offlinePlan samplerBatchMemory offlineSchedule
  Wire.encoding publicValue

/-- The setup body receives only the public parameter and byte count. -/
def compiledSetupBase (parameter : Nat) : Memory :=
  {bits := fun index => if index = 0 then natural parameter ++ natural 8887896 else []}

/-- The setup state retains its memory and complete execution charge. -/
def compiledSetupState (attempts : Nat) (result : Memory × Nat) : State :=
  ⟨executeLinear publicWireProgram result.1,
    (compiledMachine attempts).size + 1 + (result.2 + publicWireProgram.length + 5), 0⟩

/-- The joint setup law keeps the actual machine state and its complete typed source coin. -/
def compiledSetupJoint (attempts parameter : Nat) : PMF (State × SimulatorSampling.OfflineCoin) :=
  (offlineSourceJoint attempts (offlineInitialMemory (compiledSetupBase parameter))).map fun result =>
    (compiledSetupState attempts result.1, result.2)

/-- The joint setup law has the exact actual response as its first observation. -/
theorem compiledSetupJoint_machine [FieldCertificate] (attempts parameter : Nat)
    (attemptFits : attempts < 2 ^ 256)
    (enough : (initial (compiledMachine attempts)).spent +
      (2 + (batchStepBudget attempts * 838208 + publicWireProgram.length + 3)) ≤ budget 0) :
    (compiledSetupJoint attempts parameter).map (fun result => some (result.1.memory.bits 3, result.1)) =
      respond (compiledMachine attempts) ([false, false] ++ natural parameter ++ natural 8887896)
        (initial (compiledMachine attempts)) := by
  rw [compiledMachine_setupResponse attempts parameter attemptFits enough]
  simp only [compiledSetupJoint, offlineSourceJoint, PMF.map_comp, Function.comp_def]
  rfl

/-- The second joint marginal is the exact bounded private source law. -/
theorem compiledSetupJoint_source [FieldCertificate] (attempts parameter : Nat) :
    (compiledSetupJoint attempts parameter).map Prod.snd = (SimulatorSampling.offline.total attempts).law := by
  simpa only [compiledSetupJoint, PMF.map_comp, Function.comp_def] using
    offlineSourceJoint_source attempts (offlineInitialMemory (compiledSetupBase parameter))

/-- Every setup joint result retains all private words and the empty public oracle source. -/
theorem compiledSetupJoint_memory [FieldCertificate] (attempts parameter : Nat)
    (state : State) (coin : SimulatorSampling.OfflineCoin)
    (supported : (state, coin) ∈ (compiledSetupJoint attempts parameter).support)
    (metadata : SharedSimulatorMachine.Metadata) (empty : metadata.fixedTranscript = []) :
    SharedSourceMemory state.memory (initialSharedOracleSource metadata) 0 ∧
      WordsAt state.memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin) ∧
      (initialSharedOracleSource metadata).family.hash = [] ∧ state.queries = 0 := by
  obtain ⟨result, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases same
  have represented := offlineSourceJoint_initialMemory attempts (compiledSetupBase parameter)
    result.1.1 result.1.2 result.2 (by intros; rfl) member metadata empty
  exact ⟨represented.1, represented.2.1, represented.2.2, rfl⟩

/-- Every setup joint result pays only for the complete table and the actual sampler and serializer. -/
theorem compiledSetupJoint_cost [FieldCertificate] (attempts parameter : Nat)
    (state : State) (coin : SimulatorSampling.OfflineCoin)
    (supported : (state, coin) ∈ (compiledSetupJoint attempts parameter).support) :
    state.spent ≤ (compiledMachine attempts).size + 1 +
      (batchStepBudget attempts * 838208 + publicWireProgram.length + 5) := by
  obtain ⟨result, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases same
  have actual : result.1 ∈ (samplerBatchMemory offlinePlan attempts 838208 0
      (offlineInitialMemory (compiledSetupBase parameter))).support := by
    rw [← offlineSourceJoint_machine]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  exact Nat.add_le_add_left
    (Nat.add_le_add_right (Nat.add_le_add_right
      (samplerBatchMemory_cost offlinePlan attempts 838208 0
        (offlineInitialMemory (compiledSetupBase parameter)) result.1.1 result.1.2 actual) _) _) _

/-- The serializer returns the exact public bytes of each supported typed source coin. -/
theorem compiledSetupJoint_public [FieldCertificate] (attempts parameter : Nat)
    (state : State) (coin : SimulatorSampling.OfflineCoin)
    (supported : (state, coin) ∈ (compiledSetupJoint attempts parameter).support) :
    publicValue Wire.encoding 8887896 (state.memory.bits 3) = some (publicSourceTable coin.1) := by
  obtain ⟨result, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases same
  have actual : result.1 ∈ (samplerBatchMemory offlinePlan attempts 838208 0
      (offlineInitialMemory (compiledSetupBase parameter))).support := by
    rw [← offlineSourceJoint_machine]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  have stored := offlineSourceJoint_words attempts (offlineInitialMemory (compiledSetupBase parameter))
    result.1.1 result.1.2 result.2 member
  have pointer := samplerBatchMemory_caller offlinePlan attempts 838208 0
    (offlineInitialMemory (compiledSetupBase parameter)) result.1.1 result.1.2 11 (by decide) actual
  have bitsSaved := samplerBatchMemory_bits offlinePlan attempts 838208 0
    (offlineInitialMemory (compiledSetupBase parameter)) result.1.1 result.1.2 actual
  have pointers : result.1.1.registers 11 = (offlineInitialMemory (compiledSetupBase parameter)).registers 10 := by
    rw [pointer]
    simp [offlineInitialMemory]
  rw [← pointers] at stored
  change publicValue Wire.encoding 8887896 ((executeLinear publicWireProgram result.1.1).bits 3) = _
  rw [publicWireProgram_bits result.2 result.1.1 stored, Function.update_self, bitsSaved]
  simp only [offlineInitialMemory, compiledSetupBase, if_neg (by decide : (3 : Fin 4) ≠ 0), List.append_nil]
  exact publicValue_bytes Wire.encoding (publicSourceTable result.2.1) 8887896 (publicSourceTable_length result.2.1)

/-- The parsed setup response has the exact joint public table and machine state law. -/
theorem compiledSetupJoint_parsed [FieldCertificate] (attempts parameter : Nat)
    (attemptFits : attempts < 2 ^ 256)
    (enough : (initial (compiledMachine attempts)).spent +
      (2 + (batchStepBudget attempts * 838208 + publicWireProgram.length + 3)) ≤ budget 0) :
    (compiledSetupJoint attempts parameter).map (fun result => some (publicSourceTable result.2.1, result.1)) =
      (respond (compiledMachine attempts) ([false, false] ++ natural parameter ++ natural 8887896)
        (initial (compiledMachine attempts))).map (fun result => result.bind fun result =>
          (publicValue Wire.encoding 8887896 result.1).map fun table => (table, result.2)) := by
  rw [← compiledSetupJoint_machine attempts parameter attemptFits enough, PMF.map_comp]
  change (compiledSetupJoint attempts parameter).bind _ = (compiledSetupJoint attempts parameter).bind _
  apply ThreePhase.bind_eq_on_support
  intro result member
  simp only [Function.comp_def, Option.bind_some, compiledSetupJoint_public attempts parameter result.1 result.2 member,
    Option.map_some]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
