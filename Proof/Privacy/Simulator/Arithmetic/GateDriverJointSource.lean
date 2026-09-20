import Proof.Privacy.Simulator.Arithmetic.GateDriverJointMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section

/-- The source executes every command after each successful cutoff step. -/
def sharedCommandListCutoff (attempts : Nat) : List SharedCommand → SharedOracleSource → PMF (Option (Unit × SharedOracleSource))
  | [], state => PMF.pure (some ((), state))
  | command :: commands, state => bindCutoff (sharedSourceCutoff attempts (.inl (.program command)) state)
      (fun result => sharedCommandListCutoff attempts commands result.2)

/-- The gate source lists its two required commands and its optional third command. -/
def sharedGateCommandList (commands : Fin 3 → SharedCommand) (third : Bool) : List SharedCommand :=
  commands 0 :: commands 1 :: if third then [commands 2] else []

/-- The source marginal of the optional third slot has its exact one-command law. -/
theorem gateThirdCoupled_source [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit) (stored : GateCommandMemory gate 2 memory (commands 2))
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) :
    (gateThirdCoupled attempts gate commands memory state).map (Option.map fun result => ((), result.2)) =
      sharedCommandListCutoff attempts [commands 2] state := by
  apply gateContinueCoupled_source attempts limit gate 2 (commands 2) gateRestoreCoupled
    (fun updated => PMF.pure (some ((), updated))) memory state represented stored room
  intro result updated _
  simp only [gateRestoreCoupled, PMF.pure_map, Option.map_some]

/-- The source marginal of the count test selects the exact saved branch. -/
theorem gateTestCoupled_source [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource) (third : Bool)
    (represented : SharedSourceMemory memory state limit) (stored : memory.ram 20 = 3 → GateCommandMemory gate 2 memory (commands 2))
    (count : memory.ram 20 = if third then 3 else 2)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) :
    (gateTestCoupled attempts gate commands memory state).map (Option.map fun result => ((), result.2)) =
      sharedCommandListCutoff attempts (if third then [commands 2] else []) state := by
  let tested := executeLinear gateDriverTest memory
  have same : tested.ram = memory.ram := rfl
  have flag : tested.registers 1 = 0 ↔ third = true := by
    rw [gateDriverTest_value, count]
    cases third <;> decide
  simp only [gateTestCoupled, PMF.map_comp, Option.map_map, Function.comp_def]
  cases third with
  | false =>
    have skipped : (executeLinear gateDriverTest memory).registers 1 ≠ 0 := by simp only [Bool.false_eq_true, iff_false] at flag; exact flag
    simp only [if_neg skipped, gateRestoreCoupled, PMF.pure_map, Option.map_some, Bool.false_eq_true, ↓reduceIte,
      sharedCommandListCutoff]
  | true =>
    have selected : (executeLinear gateDriverTest memory).registers 1 = 0 := flag.mpr rfl
    simp only [if_pos selected, ↓reduceIte]
    exact gateThirdCoupled_source attempts limit gate commands tested state
      (represented.ramEq same) ((stored (by simpa using count)).ramEq same) room

/-- The second slot retains the saved branch and executes every remaining command. -/
theorem gateSecondCoupled_source [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource) (third : Bool)
    (represented : SharedSourceMemory memory state limit)
    (stored : ∀ slot, slot.val < 2 ∨ memory.ram 20 = 3 → GateCommandMemory gate slot memory (commands slot))
    (count : memory.ram 20 = if third then 3 else 2)
    (room : 256 + 2 * (limit + 2) < 2 ^ 110) :
    (gateSecondCoupled attempts gate commands memory state).map (Option.map fun result => ((), result.2)) =
      sharedCommandListCutoff attempts (commands 1 :: if third then [commands 2] else []) state := by
  apply gateContinueCoupled_source attempts limit gate 1 (commands 1) (gateTestCoupled attempts gate commands)
    (sharedCommandListCutoff attempts (if third then [commands 2] else [])) memory state represented (stored 1 (Or.inl (by decide))) (by omega)
  intro result updated supported
  have saved : result.2.1.ram 20 = memory.ram 20 := gateDriverSlotCoupledSamples_private attempts limit gate 1
    memory state (commands 1) represented (stored 1 (Or.inl (by decide))) (by omega) 20
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) result updated supported
  exact gateTestCoupled_source attempts (limit + 1) gate commands result.2.1 updated third
    (gateDriverSlotCoupledSamples_memory attempts limit gate 1 memory state (commands 1) represented (stored 1 (Or.inl (by decide))) (by omega) result updated supported)
    (fun active => GateCommandMemory.activeAfterSlot attempts limit gate 1 memory state commands
      represented (stored 1 (Or.inl (by decide))) stored (by omega) result updated supported 2 (Or.inr active)) (saved.trans count) (by omega)

/-- The prepared gate body has the exact two-command or three-command shared source law. -/
theorem gateBodyCoupled_source [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource) (third : Bool)
    (represented : SharedSourceMemory memory state limit)
    (stored : ∀ slot, slot.val < 2 ∨ memory.ram 20 = 3 → GateCommandMemory gate slot memory (commands slot))
    (count : memory.ram 20 = if third then 3 else 2)
    (room : 256 + 2 * (limit + 3) < 2 ^ 110) :
    (gateBodyCoupled attempts gate commands memory state).map (Option.map fun result => ((), result.2)) =
      sharedCommandListCutoff attempts (sharedGateCommandList commands third) state := by
  apply gateContinueCoupled_source attempts limit gate 0 (commands 0) (gateSecondCoupled attempts gate commands)
    (sharedCommandListCutoff attempts (commands 1 :: if third then [commands 2] else [])) memory state represented (stored 0 (Or.inl (by decide))) (by omega)
  intro result updated supported
  have saved : result.2.1.ram 20 = memory.ram 20 := gateDriverSlotCoupledSamples_private attempts limit gate 0
    memory state (commands 0) represented (stored 0 (Or.inl (by decide))) (by omega) 20
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) result updated supported
  exact gateSecondCoupled_source attempts (limit + 1) gate commands result.2.1 updated third
    (gateDriverSlotCoupledSamples_memory attempts limit gate 0 memory state (commands 0) represented (stored 0 (Or.inl (by decide))) (by omega) result updated supported)
    (GateCommandMemory.activeAfterSlot attempts limit gate 0 memory state commands
      represented (stored 0 (Or.inl (by decide))) stored (by omega) result updated supported) (saved.trans count) (by omega)

/-- The full coupled driver has the exact shared source law after deterministic preparation. -/
theorem gateDriverCoupled_source [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource) (third : Bool)
    (represented : SharedSourceMemory (gateDriverPrepared gate memory) state limit)
    (stored : ∀ slot, slot.val < 2 ∨ (gateDriverPrepared gate memory).ram 20 = 3 →
      GateCommandMemory gate slot (gateDriverPrepared gate memory) (commands slot))
    (count : (gateDriverPrepared gate memory).ram 20 = if third then 3 else 2)
    (room : 256 + 2 * (limit + 3) < 2 ^ 110) :
    (gateDriverCoupled attempts gate commands memory state).map (Option.map fun result => ((), result.2)) =
      sharedCommandListCutoff attempts (sharedGateCommandList commands third) state := by
  simpa only [gateDriverCoupled, PMF.map_comp, Option.map_map, Function.comp_def] using
    gateBodyCoupled_source attempts limit gate commands (gateDriverPrepared gate memory) state third represented stored count room

end
end Kriterion.ArgoMAC.ArithmeticSimulator
