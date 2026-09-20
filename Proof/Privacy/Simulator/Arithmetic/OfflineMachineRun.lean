import Proof.Privacy.Simulator.Arithmetic.OfflineMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine
set_option maxRecDepth 4096
attribute [local irreducible] publicWireProgram offlinePlan samplerBatchMemory

/-- The address loads select the fixed private RAM region. -/
def offlineInitialMemory (base : Memory) : Memory :=
  {base with
    registers := Function.update (Function.update base.registers 10 (BitVec.ofNat 256 privateBase)) 11 (BitVec.ofNat 256 privateBase)}

/-- The complete machine establishes both source addresses in two instructions. -/
theorem offlineMachine_entry [FieldCertificate] (attempts fuel : Nat) (base : Memory) :
    run (offlineMachine attempts) (fuel + 2) ⟨⟨0, Nat.zero_lt_succ _⟩, base⟩ =
      (run (offlineMachine attempts) fuel ⟨offlineBatchLabel 0, offlineInitialMemory base⟩).map
        (Option.map fun result => (result.1, result.2 + 2)) := by
  have entryLaw : runPrefix (offlineMachine attempts) 2 ⟨⟨0, Nat.zero_lt_succ _⟩, base⟩ =
      PMF.pure (some (false, ⟨offlineBatchLabel 0, offlineInitialMemory base⟩, 2)) := by
    simp only [runPrefix, step, offlineMachine, Vector.getElem_ofFn, offlineInitialMemory,
      Fin.val_zero, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte, PMF.pure_bind, PMF.pure_map, Option.map_some]
  rw [show fuel + 2 = 2 + fuel by omega, run_after_prefix, entryLaw, PMF.pure_bind]

/-- The serializer consumes its fixed instruction count and then halts. -/
theorem offlineMachine_emit [FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (offlineMachine attempts) (publicWireProgram.length + fuel + 1) ⟨offlineWireLabel 0, memory⟩ =
      PMF.pure (some (⟨offlineWireLabel publicWireProgram.length, executeLinear publicWireProgram memory⟩,
        publicWireProgram.length + 1)) := by
  rw [Nat.add_assoc, linear_continue (offlineMachine attempts) publicWireProgram offlineWireLabel
    (offlineMachine_wire attempts), offlineMachine_halt, PMF.pure_map]
  simp only [Option.map_some, Nat.add_comm]

/-- The batch and serializer compose with one shared instruction budget. -/
theorem offlineMachine_body [FieldCertificate] (attempts : Nat) (base : Memory)
    (countFits : attempts < 2 ^ 256) :
    run (offlineMachine attempts) (batchStepBudget attempts * 838208 + publicWireProgram.length + 1)
      ⟨offlineBatchLabel 0, base⟩ =
      (samplerBatchMemory offlinePlan attempts 838208 0 base).map fun result =>
        some (⟨offlineWireLabel publicWireProgram.length, executeLinear publicWireProgram result.1⟩,
          result.2 + publicWireProgram.length + 1) := by
  have continued := samplerBatchBlock_run (offlineMachine attempts) offlinePlan attempts (by decide)
    offlineBatchLabel (offlineMachine_batch attempts) 838208 0 (publicWireProgram.length + 1) base
    (by decide) countFits
  simp only [Nat.zero_add] at continued
  rw [Nat.add_assoc]
  apply continued.trans
  change (samplerBatchMemory offlinePlan attempts 838208 0 base).bind _ =
    (samplerBatchMemory offlinePlan attempts 838208 0 base).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨memory, cost⟩
  have bounded := samplerBatchMemory_cost offlinePlan attempts 838208 0 base memory cost supported
  have amount : batchStepBudget attempts * 838208 + (publicWireProgram.length + 1) - cost =
      publicWireProgram.length + (batchStepBudget attempts * 838208 - cost) + 1 := by omega
  have boundary : offlineBatchLabel (batchBoundary 838208 (by decide)) = offlineWireLabel 0 := by
    apply Fin.ext
    simp [offlineBatchLabel, batchBoundary, offlineWireLabel]
  rw [amount, boundary, offlineMachine_emit, PMF.pure_map]
  simp only [Function.comp_def, Option.map_some, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The complete offline machine returns its exact memory and executed cost law. -/
theorem offlineMachine_run [FieldCertificate] (attempts : Nat) (base : Memory)
    (countFits : attempts < 2 ^ 256) :
    run (offlineMachine attempts) (batchStepBudget attempts * 838208 + publicWireProgram.length + 3)
      ⟨⟨0, Nat.zero_lt_succ _⟩, base⟩ =
      (samplerBatchMemory offlinePlan attempts 838208 0 (offlineInitialMemory base)).map fun result =>
        some (⟨offlineWireLabel publicWireProgram.length, executeLinear publicWireProgram result.1⟩,
          result.2 + publicWireProgram.length + 3) := by
  rw [show batchStepBudget attempts * 838208 + publicWireProgram.length + 3 =
    (batchStepBudget attempts * 838208 + publicWireProgram.length + 1) + 2 by omega,
    offlineMachine_entry, offlineMachine_body attempts (offlineInitialMemory base) countFits,
    PMF.map_comp]
  simp only [Function.comp_def, Option.map_some, Nat.add_assoc]

/-- The offline budget pays for all source draws, all wire writes, and the full table. -/
theorem offlineMachine_budget :
    (offlineMachine 256).size + 1 +
      (batchStepBudget 256 * 838208 + publicWireProgram.length + 3) ≤ 605084290688 := by
  have bound := publicWireMachine_budget
  change publicWireProgram.length + 1 + (publicWireProgram.length + 1) ≤ 477065504 at bound
  change offlineMachineSize + 1 + _ ≤ _
  unfold offlineMachineSize batchStepBudget
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
