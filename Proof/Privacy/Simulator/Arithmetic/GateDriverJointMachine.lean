import Proof.Privacy.Simulator.Arithmetic.GateDriverJoint

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section

/-- Equal RAM preserves the complete source relation. -/
theorem SharedSourceMemory.ramEq {memory updated : Memory} {state : SharedOracleSource} {limit : Nat}
    (represented : SharedSourceMemory memory state limit) (same : updated.ram = memory.ram) :
    SharedSourceMemory updated state limit := by
  exact ⟨same ▸ represented.family, represented.capacity, same ▸ represented.history, represented.counts⟩

/-- Equal RAM preserves a stored gate command. -/
theorem GateCommandMemory.ramEq {gate : GateCode} {slot : Fin 3} {memory updated : Memory} {command : SharedCommand}
    (stored : GateCommandMemory gate slot memory command) (same : updated.ram = memory.ram) :
    GateCommandMemory gate slot updated command :=
  ⟨stored.index, (congrFun same 16).trans stored.operand, (congrFun same _).trans stored.target⟩

/-- The optional third slot has the exact machine marginal. -/
theorem gateThirdCoupled_machine [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit) (stored : GateCommandMemory gate 2 memory (commands 2))
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256) :
    (gateThirdCoupled attempts gate commands memory state).map (Option.map Prod.fst) =
      (gateThirdSamples attempts gate memory).map (fun result => if result.1 = 1035 then none else some result) := by
  apply gateContinueCoupled_machine attempts limit gate 2 (commands 2) gateRestoreCoupled gateRestoreSamples
    memory state represented stored room attemptFits
  intro result updated _
  simp only [gateRestoreCoupled, gateRestoreSamples, PMF.pure_map]
  rfl

/-- The saved count test has the exact machine marginal. -/
theorem gateTestCoupled_machine [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit) (stored : memory.ram 20 = 3 → GateCommandMemory gate 2 memory (commands 2))
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256) :
    (gateTestCoupled attempts gate commands memory state).map (Option.map Prod.fst) =
      (gateTestSamples attempts gate memory).map (fun result => if result.1 = 1035 then none else some result) := by
  let tested := executeLinear gateDriverTest memory
  have same : tested.ram = memory.ram := rfl
  have branch :
      (if tested.registers 1 = 0 then gateThirdCoupled attempts gate commands tested state else gateRestoreCoupled tested state).map
        (Option.map Prod.fst) =
      (if tested.registers 1 = 0 then gateThirdSamples attempts gate tested else gateRestoreSamples tested).map
        (fun result => if result.1 = 1035 then none else some result) := by
    split
    · rename_i selected
      have count : memory.ram 20 = 3 := by
        change (executeLinear gateDriverTest memory).registers 1 = 0 at selected
        rw [gateDriverTest_value] at selected
        exact BitVec.xor_eq_zero_iff.mp selected
      exact gateThirdCoupled_machine attempts limit gate commands tested state
        (represented.ramEq same) ((stored count).ramEq same) room attemptFits
    · simp only [gateRestoreCoupled, gateRestoreSamples, PMF.pure_map]
      rfl
  have mapped := congrArg (PMF.map (Option.map fun result : Fin 1036 × Memory × Nat =>
    (result.1, result.2.1, 5 + result.2.2))) branch
  simp only [gateTestCoupled, gateTestSamples, PMF.map_comp, Option.map_map, Function.comp_def] at mapped ⊢
  rw [mapped]
  apply congrArg (fun f => PMF.map f (if tested.registers 1 = 0 then gateThirdSamples attempts gate tested else gateRestoreSamples tested))
  funext result
  split <;> rfl

/-- The second slot and its saved count test have the exact machine marginal. -/
theorem gateSecondCoupled_machine [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit)
    (stored : ∀ slot, slot.val < 2 ∨ memory.ram 20 = 3 → GateCommandMemory gate slot memory (commands slot))
    (room : 256 + 2 * (limit + 2) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256) :
    (gateSecondCoupled attempts gate commands memory state).map (Option.map Prod.fst) =
      (gateSecondSamples attempts gate memory).map (fun result => if result.1 = 1035 then none else some result) := by
  apply gateContinueCoupled_machine attempts limit gate 1 (commands 1) (gateTestCoupled attempts gate commands)
    (gateTestSamples attempts gate) memory state represented (stored 1 (Or.inl (by decide))) (by omega) attemptFits
  intro result updated supported
  exact gateTestCoupled_machine attempts (limit + 1) gate commands result.2.1 updated
    (gateDriverSlotCoupledSamples_memory attempts limit gate 1 memory state (commands 1) represented (stored 1 (Or.inl (by decide))) (by omega) result updated supported)
    (fun active => GateCommandMemory.activeAfterSlot attempts limit gate 1 memory state commands
      represented (stored 1 (Or.inl (by decide))) stored (by omega) result updated supported 2 (Or.inr active)) (by omega) attemptFits

/-- The complete prepared gate body has the exact machine marginal. -/
theorem gateBodyCoupled_machine [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit)
    (stored : ∀ slot, slot.val < 2 ∨ memory.ram 20 = 3 → GateCommandMemory gate slot memory (commands slot))
    (room : 256 + 2 * (limit + 3) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256) :
    (gateBodyCoupled attempts gate commands memory state).map (Option.map Prod.fst) =
      (gateBodySamples attempts gate memory).map (fun result => if result.1 = 1035 then none else some result) := by
  apply gateContinueCoupled_machine attempts limit gate 0 (commands 0) (gateSecondCoupled attempts gate commands)
    (gateSecondSamples attempts gate) memory state represented (stored 0 (Or.inl (by decide))) (by omega) attemptFits
  intro result updated supported
  exact gateSecondCoupled_machine attempts (limit + 1) gate commands result.2.1 updated
    (gateDriverSlotCoupledSamples_memory attempts limit gate 0 memory state (commands 0) represented (stored 0 (Or.inl (by decide))) (by omega) result updated supported)
    (GateCommandMemory.activeAfterSlot attempts limit gate 0 memory state commands
      represented (stored 0 (Or.inl (by decide))) stored (by omega) result updated supported) (by omega) attemptFits

/-- The full coupled driver retains the compiled gate's memory and exact instruction count. -/
theorem gateDriverCoupled_machine [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory (gateDriverPrepared gate memory) state limit)
    (stored : ∀ slot, slot.val < 2 ∨ (gateDriverPrepared gate memory).ram 20 = 3 →
      GateCommandMemory gate slot (gateDriverPrepared gate memory) (commands slot))
    (room : 256 + 2 * (limit + 3) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256) :
    (gateDriverCoupled attempts gate commands memory state).map (Option.map Prod.fst) =
      (gateDriverSamples attempts gate memory).map (fun result => if result.1 = 1035 then none else some result) := by
  have body := gateBodyCoupled_machine attempts limit gate commands (gateDriverPrepared gate memory) state represented stored room attemptFits
  have mapped := congrArg (PMF.map (Option.map fun result : Fin 1036 × Memory × Nat =>
    (result.1, result.2.1, gateDriverPrefixCost gate memory + result.2.2))) body
  simp only [gateDriverCoupled, gateDriverSamples, PMF.map_comp, Option.map_map, Function.comp_def] at mapped ⊢
  rw [mapped]
  apply congrArg (fun f => PMF.map f (gateBodySamples attempts gate (gateDriverPrepared gate memory)))
  funext result
  split <;> rfl

end
end Kriterion.ArgoMAC.ArithmeticSimulator
