import Proof.Privacy.Simulator.Arithmetic.SharedParsedGame
import Proof.Privacy.Simulator.Arithmetic.CompiledMachine
import Proof.Privacy.Simulator.Arithmetic.OfflineSourceJoint

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security
noncomputable section
attribute [local irreducible] publicWireProgram offlinePlan samplerBatchMemory offlineSchedule
  Wire.encoding publicValue

/-- The serializer retains every private word and public header. -/
theorem publicWireProgram_ram (memory : Memory) :
    (executeLinear publicWireProgram memory).ram = memory.ram := by
  rw [publicWireProgram_eq]
  exact (wireSegments_preserves publicWire memory).1

/-- The setup body receives only the public parameter and byte count. -/
def compiledSetupBase (parameter : Nat) : Memory :=
  {bits := fun index => if index = 0 then natural parameter ++ natural 8887896 else []}


end
end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security
noncomputable section
attribute [local irreducible] publicWireProgram offlinePlan samplerBatchMemory offlineSchedule
  Wire.encoding publicValue

/-- The fixed-oracle setup retains only private memory and its typed coin. -/
def lazySetupJoint (parameter : Nat) : PMF (Memory × SimulatorSampling.OfflineCoin) :=
  (offlineSourceJoint 256 (offlineInitialMemory (compiledSetupBase parameter))).map fun result =>
    (executeLinear publicWireProgram result.1.1, result.2)

/-- The setup coin has the exact finite private sampling law. -/
theorem lazySetupJoint_source [FieldCertificate] (parameter : Nat) :
    (lazySetupJoint parameter).map Prod.snd = (SimulatorSampling.offline.total 256).law := by
  simpa only [lazySetupJoint, PMF.map_comp, Function.comp_def] using
    offlineSourceJoint_source 256 (offlineInitialMemory (compiledSetupBase parameter))

/-- The complete setup run has the joint source's memory marginal. -/
theorem lazySetupJoint_machine [FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] (parameter : Nat)
    (oracle : LazyOracle.State FixedIndex EncIndex) :
    (simulatorMemoryRun lazyCompiledMachine lazyCompiledMachine.firstFuel
      {bits := fun index => if index = 0 then [false, false] ++ natural parameter ++ natural 8887896 else []}
      oracle).map (Option.map fun result => (result.1, result.2.1)) =
    (lazySetupJoint parameter).map (fun result => some (result.1, oracle)) := by
  let memory : Memory := {bits := fun index =>
    if index = 0 then [false, false] ++ natural parameter ++ natural 8887896 else []}
  have wire : memory.bits 0 = false :: false :: (natural parameter ++ natural 8887896) := by simp [memory]
  have dispatched : phaseDispatchMemory memory (natural parameter ++ natural 8887896) = compiledSetupBase parameter := by
    dsimp [phaseDispatchMemory, memory, compiledSetupBase]
    congr 1
    funext index
    simp only [Function.update_apply]
    split_ifs <;> rfl
  have machine := lazyCompiledMachine_setupRun memory _ wire oracle
  rw [dispatched] at machine
  change (simulatorMemoryRun lazyCompiledMachine lazyCompiledMachine.firstFuel memory oracle).map _ = _
  rw [machine]
  unfold lazySetupJoint
  rw [PMF.map_comp, PMF.map_comp]
  have law := congrArg (PMF.map fun result : Memory × Nat =>
    some (executeLinear publicWireProgram result.1, oracle))
    (offlineSourceJoint_machine 256 (offlineInitialMemory (compiledSetupBase parameter)))
  simpa only [PMF.map_comp, Function.comp_def, Option.map_some] using law.symm

/-- Every setup result retains all private words. -/
theorem lazySetupJoint_words [FieldCertificate] (parameter : Nat) (memory : Memory)
    (coin : SimulatorSampling.OfflineCoin) (supported : (memory, coin) ∈ (lazySetupJoint parameter).support) :
    WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin) := by
  obtain ⟨result, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases same
  rw [publicWireProgram_ram]
  have stored := offlineSourceJoint_words 256 (offlineInitialMemory (compiledSetupBase parameter))
    result.1.1 result.1.2 result.2 member
  simpa only [offlineInitialMemory, Function.update_of_ne (by decide : (10 : Register) ≠ 11),
    Function.update_self] using stored

/-- The public parser recovers the complete sampled table. -/
theorem lazySetupJoint_public [FieldCertificate] (parameter : Nat) (memory : Memory)
    (coin : SimulatorSampling.OfflineCoin) (supported : (memory, coin) ∈ (lazySetupJoint parameter).support) :
    publicValue Wire.encoding 8887896 (memory.bits 3) = some (publicSourceTable coin.1) := by
  obtain ⟨result, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases same
  have actual : result.1 ∈ (samplerBatchMemory offlinePlan 256 838208 0
      (offlineInitialMemory (compiledSetupBase parameter))).support := by
    rw [← offlineSourceJoint_machine]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  have stored := offlineSourceJoint_words 256 (offlineInitialMemory (compiledSetupBase parameter))
    result.1.1 result.1.2 result.2 member
  have pointer := samplerBatchMemory_caller offlinePlan 256 838208 0
    (offlineInitialMemory (compiledSetupBase parameter)) result.1.1 result.1.2 11 (by decide) actual
  have bitsSaved := samplerBatchMemory_bits offlinePlan 256 838208 0
    (offlineInitialMemory (compiledSetupBase parameter)) result.1.1 result.1.2 actual
  have pointers : result.1.1.registers 11 = (offlineInitialMemory (compiledSetupBase parameter)).registers 10 := by
    rw [pointer]
    simp [offlineInitialMemory]
  rw [← pointers] at stored
  rw [publicWireProgram_bits result.2 result.1.1 stored, Function.update_self, bitsSaved]
  simp only [offlineInitialMemory, compiledSetupBase, if_neg (by decide : (3 : Fin 4) ≠ 0), List.append_nil]
  exact publicValue_bytes Wire.encoding (publicSourceTable result.2.1) 8887896 (publicSourceTable_length result.2.1)

end
end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security
noncomputable section

/-- The parsed setup law keeps the complete private joint source. -/
theorem lazySetupJoint_parsed [FieldCertificate] (parameter : Nat) :
    lazyParsedSetup lazyCompiledMachine parameter =
      (lazySetupJoint parameter).map (fun setup =>
        some (publicSourceTable setup.2.1, setup.1,
          (LazyOracle.empty : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex))) := by
  let parse (result : Option (Memory × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)) :=
    result.bind fun result => (publicValue Wire.encoding 8887896 (result.1.bits 3)).map
      fun table => (table, result.1, result.2)
  have law := congrArg (PMF.map parse) (lazySetupJoint_machine parameter
    (LazyOracle.empty : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex))
  simp only [PMF.map_comp] at law
  have left : lazyParsedSetup lazyCompiledMachine parameter =
      (simulatorMemoryRun lazyCompiledMachine lazyCompiledMachine.firstFuel
        {bits := fun index => if index = 0 then [false, false] ++ natural parameter ++ natural 8887896 else []}
        (LazyOracle.empty : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)).map
        (parse ∘ Option.map fun result => (result.1, result.2.1)) := by
    unfold lazyParsedSetup
    congr 1
    funext result
    cases result <;> rfl
  rw [left, law]
  change (lazySetupJoint parameter).bind _ = (lazySetupJoint parameter).bind _
  apply ThreePhase.bind_eq_on_support
  intro setup member
  simp only [Function.comp_def, parse, Option.bind_some,
    lazySetupJoint_public parameter setup.1 setup.2 member, Option.map_some]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
