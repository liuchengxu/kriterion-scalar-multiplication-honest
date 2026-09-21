import Proof.Privacy.Simulator.StrictOracleLaw
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

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine

set_option backward.isDefEq.respectTransparency false in
theorem lazyGateDriverResult_oracle (gate : GateCode) (memory : Memory)
    (commands : Fin 3 → SharedCommand) (third : Bool)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (stored : ∀ slot, slot.val < 2 ∨ (gateDriverPrepared gate memory).ram 20 = 3 →
      GateCommandMemory gate slot (gateDriverPrepared gate memory) (commands slot))
    (count : (gateDriverPrepared gate memory).ram 20 = if third then 3 else 2) :
    (lazyGateDriverResult gate memory oracle).map (fun result => result.2.1) =
      strictCommands oracle (sharedGateCommandList commands third) := by
  let ready := gateDriverPrepared gate memory
  have firstLaw := lazyGateSlot_oracle gate 0 ready (commands 0) (stored 0 (Or.inl (by decide))) oracle
  unfold lazyGateDriverResult
  dsimp only [Bind.bind]
  cases firstEq : lazyGateSlot gate 0 ready oracle with
  | none =>
    have failed : LazyOracle.program (.fixedForward (commands 0).1 (commands 0).2.1)
        (commands 0).2.2 oracle = none := by simpa [firstEq] using firstLaw.symm
    simp only [show gateDriverPrepared gate memory = ready from rfl, firstEq, Option.bind_none, Option.map_none]
    simp [sharedGateCommandList, strictCommands, failed]
  | some first =>
    have firstProgram : LazyOracle.program (.fixedForward (commands 0).1 (commands 0).2.1)
        (commands 0).2.2 oracle = some first.2 := by simpa [firstEq] using firstLaw.symm
    have firstSaved := lazyGateSlot_scratch firstEq
    have firstCount : first.1.ram 20 = ready.ram 20 := firstSaved 20 (by decide)
    have firstStored : ∀ slot, slot.val < 2 ∨ first.1.ram 20 = 3 →
        GateCommandMemory gate slot first.1 (commands slot) := by
      intro slot active
      exact (stored slot (active.imp_right (fun eq => firstCount.symm.trans eq))).scratchEq firstSaved
    have secondLaw := lazyGateSlot_oracle gate 1 first.1 (commands 1)
      (firstStored 1 (Or.inl (by decide))) first.2
    simp only [show gateDriverPrepared gate memory = ready from rfl, firstEq, Option.bind_some]
    cases secondEq : lazyGateSlot gate 1 first.1 first.2 with
    | none =>
      have failed : LazyOracle.program (.fixedForward (commands 1).1 (commands 1).2.1)
          (commands 1).2.2 first.2 = none := by simpa [secondEq] using secondLaw.symm
      simp [sharedGateCommandList, strictCommands, firstProgram, failed]
    | some second =>
      simp only [Option.bind_some]
      have secondProgram : LazyOracle.program (.fixedForward (commands 1).1 (commands 1).2.1)
          (commands 1).2.2 first.2 = some second.2 := by simpa [secondEq] using secondLaw.symm
      have secondSaved := lazyGateSlot_scratch secondEq
      have secondCount : second.1.ram 20 = ready.ram 20 := (secondSaved 20 (by decide)).trans firstCount
      let tested := executeLinear gateDriverTest second.1
      have flag : tested.registers 1 = 0 ↔ third = true := by
        rw [gateDriverTest_value, secondCount, count]
        cases third <;> decide
      cases third with
      | false =>
        have skipped : tested.registers 1 ≠ 0 := by simpa using flag
        rw [if_neg skipped]
        simp [sharedGateCommandList, strictCommands, firstProgram, secondProgram]
      | true =>
        have selected : tested.registers 1 = 0 := flag.mpr rfl
        have lastStored : GateCommandMemory gate 2 tested (commands 2) := by
          apply (firstStored 2 (Or.inr (firstCount.trans count))).scratchEq
          exact secondSaved
        have thirdLaw := lazyGateSlot_oracle gate 2 tested (commands 2) lastStored second.2
        rw [if_pos selected]
        simp only [sharedGateCommandList, strictCommands, firstProgram, secondProgram]
        cases thirdEq : lazyGateSlot gate 2 tested second.2 <;>
          simp_all [tested, strictCommands]


end Kriterion.ArgoMAC.ArithmeticSimulator
