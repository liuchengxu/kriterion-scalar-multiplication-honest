import Proof.Privacy.Simulator.Arithmetic.GateDriverJointPrivate
import Proof.Privacy.Simulator.Arithmetic.GatePreparedMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine
noncomputable section

/-- A normal gate return restores each caller register from its saved word. -/
def GateCallerRestored (memory : Memory) : Prop :=
  memory.registers 11 = memory.ram 21 ∧ memory.registers 12 = memory.ram 22 ∧
  memory.registers 13 = memory.ram 23 ∧ memory.registers 14 = memory.ram 24 ∧ memory.registers 15 = memory.ram 25

/-- The return block restores all five caller registers. -/
theorem gateRestoreCoupled_caller (memory : Memory) (state : SharedOracleSource) (result : GateJointResult)
    (supported : some result ∈ (gateRestoreCoupled memory state).support) : GateCallerRestored result.1.2.1 := by
  simp only [gateRestoreCoupled, PMF.mem_support_pure_iff, Option.some.injEq] at supported
  subst result
  have saved := gateDirectiveRestore_values memory
  unfold GateCallerRestored
  rw [(gateDirectiveRestore_data memory).1]
  exact saved

/-- A slot preserves every final-memory property of its accepted continuation. -/
theorem gateContinueCoupled_property (attempts : Nat) (gate : GateCode) (slot : Fin 3) (command : SharedCommand)
    (next : Memory → SharedOracleSource → PMF (Option GateJointResult)) (property : Memory → Prop)
    (nextProperty : ∀ memory state result, some result ∈ (next memory state).support → property result.1.2.1)
    (memory : Memory) (state : SharedOracleSource) (result : GateJointResult)
    (supported : some result ∈ (gateContinueCoupled attempts gate slot command next memory state).support) :
    property result.1.2.1 := by
  obtain ⟨actual, updated, tail, _, returned, rfl⟩ := gateContinueCoupled_support attempts gate slot command next memory state result supported
  exact nextProperty actual.2.1 updated tail returned

/-- Every accepted prepared gate body restores its five caller registers. -/
theorem gateBodyCoupled_caller (attempts : Nat) (gate : GateCode) (commands : Fin 3 → SharedCommand)
    (memory : Memory) (state : SharedOracleSource) (result : GateJointResult)
    (supported : some result ∈ (gateBodyCoupled attempts gate commands memory state).support) : GateCallerRestored result.1.2.1 := by
  have third : ∀ memory state result, some result ∈ (gateThirdCoupled attempts gate commands memory state).support →
      GateCallerRestored result.1.2.1 := by
    intro memory state result supported
    exact gateContinueCoupled_property attempts gate 2 (commands 2) gateRestoreCoupled GateCallerRestored
      gateRestoreCoupled_caller memory state result supported
  have test : ∀ memory state result, some result ∈ (gateTestCoupled attempts gate commands memory state).support →
      GateCallerRestored result.1.2.1 := by
    intro memory state result supported
    obtain ⟨draw, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    cases draw with
    | none => simp at equal
    | some tail =>
      have same := Option.some.inj equal
      subst result
      split at reached
      · exact third _ state tail reached
      · exact gateRestoreCoupled_caller _ state tail reached
  have second : ∀ memory state result, some result ∈ (gateSecondCoupled attempts gate commands memory state).support →
      GateCallerRestored result.1.2.1 := by
    intro memory state result supported
    exact gateContinueCoupled_property attempts gate 1 (commands 1) (gateTestCoupled attempts gate commands)
      GateCallerRestored test memory state result supported
  exact gateContinueCoupled_property attempts gate 0 (commands 0) (gateSecondCoupled attempts gate commands)
    GateCallerRestored second memory state result supported

/-- Gate preparation saves the five original caller registers. -/
theorem gateDriverPrepared_caller (gate : GateCode) (memory : Memory) :
    (gateDriverPrepared gate memory).ram 21 = memory.registers 11 ∧
    (gateDriverPrepared gate memory).ram 22 = memory.registers 12 ∧
    (gateDriverPrepared gate memory).ram 23 = memory.registers 13 ∧
    (gateDriverPrepared gate memory).ram 24 = memory.registers 14 ∧
    (gateDriverPrepared gate memory).ram 25 = memory.registers 15 := by
  let loaded := executeLinear (gateDirectiveLoad gate.selected gate.target gate.quotient gate.table) memory
  let blocked := gateBlocksMemory gate.tweak (gateDriverBit gate memory) loaded
  have retained : ∀ register : Register, 11 ≤ register.val → blocked.registers register = memory.registers register := by
    intro register caller
    have branch : blocked.registers register = loaded.registers register := by
      unfold blocked gateBlocksMemory
      split
      · exact (gatePadProgram_preserves loaded gate.tweak).2.2 register (by omega)
      · exact (gateHashProgram_preserves loaded gate.tweak).2.2 register (by omega)
    exact branch.trans ((gateDirectiveLoad_preserves gate.selected gate.target gate.quotient gate.table memory).2.2 register caller)
  have saved := (gateDirectiveSave_values blocked).2.2.2.2.2
  exact ⟨saved.1.trans (retained 11 (by decide)), saved.2.1.trans (retained 12 (by decide)),
    saved.2.2.1.trans (retained 13 (by decide)), saved.2.2.2.1.trans (retained 14 (by decide)),
    saved.2.2.2.2.trans (retained 15 (by decide))⟩

/-- The complete driver preserves all five original caller registers. -/
theorem gateDriverCoupled_caller [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory (gateDriverPrepared gate memory) state limit)
    (stored : ∀ slot, slot.val < 2 ∨ (gateDriverPrepared gate memory).ram 20 = 3 →
      GateCommandMemory gate slot (gateDriverPrepared gate memory) (commands slot))
    (room : 256 + 2 * (limit + 3) < 2 ^ 110) (result : GateJointResult)
    (supported : some result ∈ (gateDriverCoupled attempts gate commands memory state).support) :
    result.1.2.1.registers 11 = memory.registers 11 ∧ result.1.2.1.registers 12 = memory.registers 12 ∧
    result.1.2.1.registers 13 = memory.registers 13 ∧ result.1.2.1.registers 14 = memory.registers 14 ∧
    result.1.2.1.registers 15 = memory.registers 15 := by
  have restored : GateCallerRestored result.1.2.1 := by
    obtain ⟨draw, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    cases draw with
    | none => simp at equal
    | some tail =>
      have same := Option.some.inj equal
      subst result
      exact gateBodyCoupled_caller attempts gate commands _ state tail reached
  have saved := gateDriverPrepared_caller gate memory
  have kept (cell : Nat) (lower : 21 ≤ cell) (upper : cell ≤ 25) :
      result.1.2.1.ram (BitVec.ofNat 256 cell) = (gateDriverPrepared gate memory).ram (BitVec.ofNat 256 cell) :=
    gateDriverCoupled_private attempts limit gate commands memory state represented stored room cell
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) result supported
  exact ⟨restored.1.trans ((kept 21 (by decide) (by decide)).trans saved.1),
    restored.2.1.trans ((kept 22 (by decide) (by decide)).trans saved.2.1),
    restored.2.2.1.trans ((kept 23 (by decide) (by decide)).trans saved.2.2.1),
    restored.2.2.2.1.trans ((kept 24 (by decide) (by decide)).trans saved.2.2.2.1),
    restored.2.2.2.2.trans ((kept 25 (by decide) (by decide)).trans saved.2.2.2.2)⟩

end
end Kriterion.ArgoMAC.ArithmeticSimulator
