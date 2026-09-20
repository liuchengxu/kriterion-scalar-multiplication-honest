import Proof.Privacy.Simulator.Arithmetic.GateDriverJointSource
import Proof.Privacy.Simulator.Arithmetic.GateSlotHash

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section

/-- A larger count cap preserves the represented source relation. -/
theorem SharedSourceMemory.mono {memory : Memory} {state : SharedOracleSource} {first second : Nat}
    (represented : SharedSourceMemory memory state first) (bounded : first ≤ second) :
    SharedSourceMemory memory state second :=
  ⟨represented.family, represented.capacity, represented.history,
    fun index => (represented.counts.1 index).trans bounded,
    fun index => (represented.counts.2.1 index).trans bounded,
    fun index => (represented.counts.2.2 index).trans bounded⟩

/-- Each accepted continuation has an accepted slot result and an accepted tail result. -/
theorem gateContinueCoupled_support (attempts : Nat) (gate : GateCode) (slot : Fin 3) (command : SharedCommand)
    (next : Memory → SharedOracleSource → PMF (Option GateJointResult)) (memory : Memory) (state : SharedOracleSource)
    (result : GateJointResult) (supported : some result ∈ (gateContinueCoupled attempts gate slot command next memory state).support) :
    ∃ actual updated tail,
      some ((), (actual, updated)) ∈ (gateDriverSlotCoupledSamples attempts gate slot memory state command).support ∧
      some tail ∈ (next actual.2.1 updated).support ∧
      result = ((tail.1.1, tail.1.2.1, actual.2.2 + tail.1.2.2), tail.2) := by
  obtain ⟨⟨value, actual, updated⟩, reached, tailReached⟩ := (mem_support_bindCutoff _ _ _).mp supported
  cases value
  obtain ⟨tail, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp tailReached
  cases tail with
  | none => simp at equal
  | some tail =>
    exact ⟨actual, updated, tail, reached, member, (Option.some.inj equal).symm⟩

/-- Every accepted third slot preserves the source relation and its unchanged hash table. -/
theorem gateThirdCoupled_memory [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit) (stored : GateCommandMemory gate 2 memory (commands 2))
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) (result : GateJointResult)
    (supported : some result ∈ (gateThirdCoupled attempts gate commands memory state).support) :
    SharedSourceMemory result.1.2.1 result.2 (limit + 1) ∧ result.2.family.hash = state.family.hash := by
  obtain ⟨actual, updated, tail, reached, returned, rfl⟩ := gateContinueCoupled_support attempts gate 2 (commands 2)
    gateRestoreCoupled memory state result supported
  simp only [gateRestoreCoupled, PMF.mem_support_pure_iff, Option.some.injEq] at returned
  subst tail
  have next := gateDriverSlotCoupledSamples_memory attempts limit gate 2 memory state (commands 2)
    represented stored room actual updated reached
  exact ⟨next.ramEq (gateDirectiveRestore_data actual.2.1).1,
    gateDriverSlotCoupledSamples_hash attempts gate 2 memory state (commands 2) actual updated reached⟩

/-- Every accepted count test preserves the source relation and its unchanged hash table. -/
theorem gateTestCoupled_memory [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit)
    (stored : memory.ram 20 = 3 → GateCommandMemory gate 2 memory (commands 2))
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) (result : GateJointResult)
    (supported : some result ∈ (gateTestCoupled attempts gate commands memory state).support) :
    SharedSourceMemory result.1.2.1 result.2 (limit + 1) ∧ result.2.family.hash = state.family.hash := by
  obtain ⟨draw, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases draw with
  | none => simp at equal
  | some tail =>
    have same := Option.some.inj equal
    subst result
    by_cases selected : (executeLinear gateDriverTest memory).registers 1 = 0
    · simp only [if_pos selected] at reached
      have count : memory.ram 20 = 3 := by rw [gateDriverTest_value] at selected; exact BitVec.xor_eq_zero_iff.mp selected
      have testedRep : SharedSourceMemory (executeLinear gateDriverTest memory) state limit := represented.ramEq rfl
      have testedStored : GateCommandMemory gate 2 (executeLinear gateDriverTest memory) (commands 2) := (stored count).ramEq rfl
      exact gateThirdCoupled_memory attempts limit gate commands (executeLinear gateDriverTest memory) state
        testedRep testedStored room tail reached
    · simp only [if_neg selected, gateRestoreCoupled, PMF.mem_support_pure_iff, Option.some.injEq] at reached
      subst tail
      have retained : SharedSourceMemory (executeLinear gateDirectiveRestore (executeLinear gateDriverTest memory)) state limit :=
        represented.ramEq ((gateDirectiveRestore_data _).1.trans rfl)
      exact ⟨retained.mono (Nat.le_succ limit), rfl⟩

/-- Every accepted second slot preserves the source relation and its unchanged hash table. -/
theorem gateSecondCoupled_memory [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit)
    (stored : ∀ slot, slot.val < 2 ∨ memory.ram 20 = 3 → GateCommandMemory gate slot memory (commands slot))
    (room : 256 + 2 * (limit + 2) < 2 ^ 110) (result : GateJointResult)
    (supported : some result ∈ (gateSecondCoupled attempts gate commands memory state).support) :
    SharedSourceMemory result.1.2.1 result.2 (limit + 2) ∧ result.2.family.hash = state.family.hash := by
  obtain ⟨actual, updated, tail, reached, returned, rfl⟩ := gateContinueCoupled_support attempts gate 1 (commands 1)
    (gateTestCoupled attempts gate commands) memory state result supported
  have next := gateDriverSlotCoupledSamples_memory attempts limit gate 1 memory state (commands 1)
    represented (stored 1 (Or.inl (by decide))) (by omega) actual updated reached
  have kept := gateTestCoupled_memory attempts (limit + 1) gate commands actual.2.1 updated next
    (fun active => GateCommandMemory.activeAfterSlot attempts limit gate 1 memory state commands represented
      (stored 1 (Or.inl (by decide))) stored (by omega) actual updated reached 2 (Or.inr active)) (by omega) tail returned
  exact ⟨by simpa only [Nat.add_assoc] using kept.1,
    kept.2.trans (gateDriverSlotCoupledSamples_hash attempts gate 1 memory state (commands 1) actual updated reached)⟩

/-- Every accepted gate body preserves the source relation and its unchanged hash table. -/
theorem gateBodyCoupled_memory [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit)
    (stored : ∀ slot, slot.val < 2 ∨ memory.ram 20 = 3 → GateCommandMemory gate slot memory (commands slot))
    (room : 256 + 2 * (limit + 3) < 2 ^ 110) (result : GateJointResult)
    (supported : some result ∈ (gateBodyCoupled attempts gate commands memory state).support) :
    SharedSourceMemory result.1.2.1 result.2 (limit + 3) ∧ result.2.family.hash = state.family.hash := by
  obtain ⟨actual, updated, tail, reached, returned, rfl⟩ := gateContinueCoupled_support attempts gate 0 (commands 0)
    (gateSecondCoupled attempts gate commands) memory state result supported
  have next := gateDriverSlotCoupledSamples_memory attempts limit gate 0 memory state (commands 0)
    represented (stored 0 (Or.inl (by decide))) (by omega) actual updated reached
  have kept := gateSecondCoupled_memory attempts (limit + 1) gate commands actual.2.1 updated next
    (GateCommandMemory.activeAfterSlot attempts limit gate 0 memory state commands represented
      (stored 0 (Or.inl (by decide))) stored (by omega) actual updated reached) (by omega) tail returned
  exact ⟨by simpa only [Nat.add_assoc] using kept.1,
    kept.2.trans (gateDriverSlotCoupledSamples_hash attempts gate 0 memory state (commands 0) actual updated reached)⟩

/-- The complete gate driver raises the count cap by at most three and preserves the hash table. -/
theorem gateDriverCoupled_memory [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory (gateDriverPrepared gate memory) state limit)
    (stored : ∀ slot, slot.val < 2 ∨ (gateDriverPrepared gate memory).ram 20 = 3 →
      GateCommandMemory gate slot (gateDriverPrepared gate memory) (commands slot))
    (room : 256 + 2 * (limit + 3) < 2 ^ 110) (result : GateJointResult)
    (supported : some result ∈ (gateDriverCoupled attempts gate commands memory state).support) :
    SharedSourceMemory result.1.2.1 result.2 (limit + 3) ∧ result.2.family.hash = state.family.hash := by
  obtain ⟨draw, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases draw with
  | none => simp at equal
  | some tail =>
    have same := Option.some.inj equal
    subst result
    exact gateBodyCoupled_memory attempts limit gate commands (gateDriverPrepared gate memory) state represented stored room tail reached

end
end Kriterion.ArgoMAC.ArithmeticSimulator
