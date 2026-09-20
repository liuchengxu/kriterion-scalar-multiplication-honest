import Proof.Privacy.Simulator.Arithmetic.GateDriverJointMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section

/-- The third slot and caller restoration preserve each caller buffer word. -/
theorem gateThirdCoupled_private (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit) (stored : GateCommandMemory gate 2 memory (commands 2))
    (room : 256 + 2 * (limit + 1) < 2 ^ 110)
    (cell : Nat) (privateBound : cell < 2 ^ 96) (lower : 15 ≤ cell)
    (not26 : cell ≠ 26) (not27 : cell ≠ 27) (not28 : cell ≠ 28) (not31 : cell ≠ 31)
    (result : GateJointResult) (supported : some result ∈ (gateThirdCoupled attempts gate commands memory state).support) :
    result.1.2.1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  obtain ⟨actual, updated, tail, reached, returned, rfl⟩ := gateContinueCoupled_support attempts gate 2 (commands 2)
    gateRestoreCoupled memory state result supported
  simp only [gateRestoreCoupled, PMF.mem_support_pure_iff, Option.some.injEq] at returned
  subst tail
  change (executeLinear gateDirectiveRestore actual.2.1).ram _ = _
  rw [(gateDirectiveRestore_data actual.2.1).1]
  exact gateDriverSlotCoupledSamples_private attempts limit gate 2 memory state (commands 2) represented stored room
    cell privateBound lower not26 not27 not28 not31 actual updated reached

/-- The saved slot-count test preserves each caller buffer word. -/
theorem gateTestCoupled_private (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit)
    (stored : memory.ram 20 = 3 → GateCommandMemory gate 2 memory (commands 2))
    (room : 256 + 2 * (limit + 1) < 2 ^ 110)
    (cell : Nat) (privateBound : cell < 2 ^ 96) (lower : 15 ≤ cell)
    (not26 : cell ≠ 26) (not27 : cell ≠ 27) (not28 : cell ≠ 28) (not31 : cell ≠ 31)
    (result : GateJointResult) (supported : some result ∈ (gateTestCoupled attempts gate commands memory state).support) :
    result.1.2.1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
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
      exact gateThirdCoupled_private attempts limit gate commands (executeLinear gateDriverTest memory) state
        testedRep testedStored room cell privateBound lower not26 not27 not28 not31 tail reached
    · simp only [if_neg selected, gateRestoreCoupled, PMF.mem_support_pure_iff, Option.some.injEq] at reached
      subst tail
      change (executeLinear gateDirectiveRestore (executeLinear gateDriverTest memory)).ram _ = _
      rw [(gateDirectiveRestore_data _).1]
      rfl

/-- The second slot and its continuation preserve each caller buffer word. -/
theorem gateSecondCoupled_private [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit)
    (stored : ∀ slot, slot.val < 2 ∨ memory.ram 20 = 3 → GateCommandMemory gate slot memory (commands slot))
    (room : 256 + 2 * (limit + 2) < 2 ^ 110)
    (cell : Nat) (privateBound : cell < 2 ^ 96) (lower : 15 ≤ cell)
    (not26 : cell ≠ 26) (not27 : cell ≠ 27) (not28 : cell ≠ 28) (not31 : cell ≠ 31)
    (result : GateJointResult) (supported : some result ∈ (gateSecondCoupled attempts gate commands memory state).support) :
    result.1.2.1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  obtain ⟨actual, updated, tail, reached, returned, rfl⟩ := gateContinueCoupled_support attempts gate 1 (commands 1)
    (gateTestCoupled attempts gate commands) memory state result supported
  have next := gateDriverSlotCoupledSamples_memory attempts limit gate 1 memory state (commands 1)
    represented (stored 1 (Or.inl (by decide))) (by omega) actual updated reached
  have kept := gateTestCoupled_private attempts (limit + 1) gate commands actual.2.1 updated next
    (fun active => GateCommandMemory.activeAfterSlot attempts limit gate 1 memory state commands represented
      (stored 1 (Or.inl (by decide))) stored (by omega) actual updated reached 2 (Or.inr active)) (by omega)
    cell privateBound lower not26 not27 not28 not31 tail returned
  exact kept.trans (gateDriverSlotCoupledSamples_private attempts limit gate 1 memory state (commands 1)
    represented (stored 1 (Or.inl (by decide))) (by omega) cell privateBound lower not26 not27 not28 not31 actual updated reached)

/-- The complete prepared gate body preserves each caller buffer word. -/
theorem gateBodyCoupled_private [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit)
    (stored : ∀ slot, slot.val < 2 ∨ memory.ram 20 = 3 → GateCommandMemory gate slot memory (commands slot))
    (room : 256 + 2 * (limit + 3) < 2 ^ 110)
    (cell : Nat) (privateBound : cell < 2 ^ 96) (lower : 15 ≤ cell)
    (not26 : cell ≠ 26) (not27 : cell ≠ 27) (not28 : cell ≠ 28) (not31 : cell ≠ 31)
    (result : GateJointResult) (supported : some result ∈ (gateBodyCoupled attempts gate commands memory state).support) :
    result.1.2.1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  obtain ⟨actual, updated, tail, reached, returned, rfl⟩ := gateContinueCoupled_support attempts gate 0 (commands 0)
    (gateSecondCoupled attempts gate commands) memory state result supported
  have next := gateDriverSlotCoupledSamples_memory attempts limit gate 0 memory state (commands 0)
    represented (stored 0 (Or.inl (by decide))) (by omega) actual updated reached
  have kept := gateSecondCoupled_private attempts (limit + 1) gate commands actual.2.1 updated next
    (GateCommandMemory.activeAfterSlot attempts limit gate 0 memory state commands represented
      (stored 0 (Or.inl (by decide))) stored (by omega) actual updated reached) (by omega)
    cell privateBound lower not26 not27 not28 not31 tail returned
  exact kept.trans (gateDriverSlotCoupledSamples_private attempts limit gate 0 memory state (commands 0)
    represented (stored 0 (Or.inl (by decide))) (by omega) cell privateBound lower not26 not27 not28 not31 actual updated reached)

/-- The complete driver retains each private word from its prepared memory. -/
theorem gateDriverCoupled_private [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory (gateDriverPrepared gate memory) state limit)
    (stored : ∀ slot, slot.val < 2 ∨ (gateDriverPrepared gate memory).ram 20 = 3 →
      GateCommandMemory gate slot (gateDriverPrepared gate memory) (commands slot))
    (room : 256 + 2 * (limit + 3) < 2 ^ 110)
    (cell : Nat) (privateBound : cell < 2 ^ 96) (lower : 15 ≤ cell)
    (not26 : cell ≠ 26) (not27 : cell ≠ 27) (not28 : cell ≠ 28) (not31 : cell ≠ 31)
    (result : GateJointResult) (supported : some result ∈ (gateDriverCoupled attempts gate commands memory state).support) :
    result.1.2.1.ram (BitVec.ofNat 256 cell) = (gateDriverPrepared gate memory).ram (BitVec.ofNat 256 cell) := by
  obtain ⟨draw, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases draw with
  | none => simp at equal
  | some tail =>
    have same := Option.some.inj equal
    subst result
    exact gateBodyCoupled_private attempts limit gate commands (gateDriverPrepared gate memory) state represented stored room
      cell privateBound lower not26 not27 not28 not31 tail reached

end
end Kriterion.ArgoMAC.ArithmeticSimulator
