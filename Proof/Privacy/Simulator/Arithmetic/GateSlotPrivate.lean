import Proof.Privacy.Simulator.Arithmetic.GateSlotInvariant

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section
set_option maxRecDepth 4096

/-- Every loaded slot preserves the saved gate words and the caller buffers. -/
theorem gateDriverSlotSamples_private (attempts limit : Nat) (gate : GateCode) (slot : Fin 3)
    (memory : Memory) (state : SharedOracleSource) (command : SharedCommand)
    (represented : SharedSourceMemory memory state limit) (stored : GateCommandMemory gate slot memory command)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110)
    (cell : Nat) (privateBound : cell < 2 ^ 96) (lower : 15 ≤ cell)
    (not26 : cell ≠ 26) (not27 : cell ≠ 27) (not28 : cell ≠ 28) (not31 : cell ≠ 31)
    (result : Fin 305 × Memory × Nat)
    (supported : result ∈ (gateDriverSlotSamples attempts gate slot memory).support) :
    result.2.1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  obtain ⟨actual, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  let loaded := executeLinear (gateSlotLoad (gate.oracle slot) slot) memory
  let oracle := sharedPhysicalIndex (.inl command.1)
  have load := gateSlotLoad_values (gate.oracle slot) slot memory
  have source := gateSlotLoad_source memory (gate.oracle slot) slot state represented.family represented.capacity
    represented.history (represented.historyFits room)
  have loadedIndex : loaded.registers 9 = BitVec.ofNat 256 oracle.val :=
    load.2.1.trans (congrArg (BitVec.ofNat 256) stored.index)
  have physicalIndex : loaded.registers 9 = BitVec.ofNat 256 oracle.castSucc.val := by
    rw [Fin.val_castSucc]
    exact loadedIndex
  have counts := checkedSlotCounts_eq loaded oracle.castSucc (state.family.permutations oracle)
    (source.1.permutations oracle) physicalIndex (represented.capacity.base oracle) (represented.capacity.overlay oracle)
  have historyCount := checkedSlotHistoryCount_eq loaded oracle.castSucc
    (recordHistoryPairs state.metadata.fixedTranscript command.1).length physicalIndex (source.2 command.1).count
    (by have := represented.counts.2.2 command.1; omega)
  change actual ∈ (checkedSlotAutomaticSamples attempts loaded).support at reached
  simp only [checkedSlotAutomaticSamples, counts.1, counts.2, historyCount] at reached
  have base := represented.counts.1 oracle
  have overlay := represented.counts.2.1 oracle
  have history := represented.counts.2.2 command.1
  have retained := checkedSlotSamples_private attempts _ _ loaded oracle.castSucc (state.family.permutations oracle)
    (source.1.permutations oracle) physicalIndex (source.2 command.1).count
    (by omega) (by omega) (by omega) cell privateBound lower not26 not27 not28 not31 actual reached
  change actual.2.1.ram _ = _
  rw [retained, load.2.2.2.1]
  have separate : BitVec.ofNat 256 cell ≠ (14 : Word) := privateWord_ne cell 14 privateBound (by decide) (by omega)
  exact Function.update_of_ne separate _ _

/-- Every accepted coupled slot preserves the saved gate words and the caller buffers. -/
theorem gateDriverSlotCoupledSamples_private (attempts limit : Nat) (gate : GateCode) (slot : Fin 3)
    (memory : Memory) (state : SharedOracleSource) (command : SharedCommand)
    (represented : SharedSourceMemory memory state limit) (stored : GateCommandMemory gate slot memory command)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110)
    (cell : Nat) (privateBound : cell < 2 ^ 96) (lower : 15 ≤ cell)
    (not26 : cell ≠ 26) (not27 : cell ≠ 27) (not28 : cell ≠ 28) (not31 : cell ≠ 31)
    (result : Fin 305 × Memory × Nat) (next : SharedOracleSource)
    (supported : some ((), (result, next)) ∈ (gateDriverSlotCoupledSamples attempts gate slot memory state command).support) :
    result.2.1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) :=
  gateDriverSlotSamples_private attempts limit gate slot memory state command represented stored room
    cell privateBound lower not26 not27 not28 not31 result
    (gateDriverSlotCoupledSamples_machineSupport attempts limit gate slot memory state command represented stored room result next supported).1

/-- A completed slot leaves every later saved command unchanged. -/
theorem GateCommandMemory.afterSlot (attempts limit : Nat) (gate : GateCode) (slot later : Fin 3)
    (memory : Memory) (state : SharedOracleSource) (command nextCommand : SharedCommand)
    (represented : SharedSourceMemory memory state limit) (stored : GateCommandMemory gate slot memory command)
    (nextStored : GateCommandMemory gate later memory nextCommand)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) (result : Fin 305 × Memory × Nat) (next : SharedOracleSource)
    (supported : some ((), (result, next)) ∈ (gateDriverSlotCoupledSamples attempts gate slot memory state command).support) :
    GateCommandMemory gate later result.2.1 nextCommand := by
  refine ⟨nextStored.index, ?_, ?_⟩
  · exact (gateDriverSlotCoupledSamples_private attempts limit gate slot memory state command represented stored room
      16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) result next supported).trans nextStored.operand
  · exact (gateDriverSlotCoupledSamples_private attempts limit gate slot memory state command represented stored room
      (17 + later.val) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) result next supported).trans nextStored.target


/-- A completed slot retains every command that the saved count can select. -/
theorem GateCommandMemory.activeAfterSlot (attempts limit : Nat) (gate : GateCode) (slot : Fin 3)
    (memory : Memory) (state : SharedOracleSource) (commands : Fin 3 → SharedCommand)
    (represented : SharedSourceMemory memory state limit) (current : GateCommandMemory gate slot memory (commands slot))
    (stored : ∀ later, later.val < 2 ∨ memory.ram 20 = 3 → GateCommandMemory gate later memory (commands later))
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) (result : Fin 305 × Memory × Nat) (next : SharedOracleSource)
    (supported : some ((), (result, next)) ∈ (gateDriverSlotCoupledSamples attempts gate slot memory state (commands slot)).support) :
    ∀ later, later.val < 2 ∨ result.2.1.ram 20 = 3 → GateCommandMemory gate later result.2.1 (commands later) := by
  intro later active
  have saved : result.2.1.ram 20 = memory.ram 20 := gateDriverSlotCoupledSamples_private attempts limit gate slot
    memory state (commands slot) represented current room 20
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) result next supported
  apply GateCommandMemory.afterSlot attempts limit gate slot later memory state (commands slot) (commands later)
    represented current (stored later (by simpa only [saved] using active)) room result next supported

end
end Kriterion.ArgoMAC.ArithmeticSimulator
