import Proof.Privacy.Simulator.Arithmetic.CheckedSlotCoupling
import Proof.Privacy.Simulator.Arithmetic.GateDriverSlot

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section
set_option maxRecDepth 4096

/-- The slot loader preserves every public oracle cell. -/
theorem gateSlotLoad_public (memory : Memory) (index : Nat) (slot : Fin 3)
    (oracle : Fin 15749) (region : Fin 4) (offset : Nat) (fits : offset < 2 ^ 110) :
    (executeLinear (gateSlotLoad index slot) memory).ram (oracleAddress oracle region offset) =
      memory.ram (oracleAddress oracle region offset) := by
  rw [(gateSlotLoad_values index slot memory).2.2.2.1]
  exact Function.update_of_ne (oracleAddress_private_disjoint oracle region offset 14 fits (by decide)) _ _

/-- The coupled slot includes its eight loader instructions. -/
def gateDriverSlotCoupledSamples (attempts : Nat) (gate : GateCode) (slot : Fin 3)
    (memory : Memory) (state : SharedOracleSource) (command : SharedCommand) :
    PMF (Option (Unit × ((Fin 305 × Memory × Nat) × SharedOracleSource))) :=
  (checkedSlotCoupledSamples attempts (executeLinear (gateSlotLoad (gate.oracle slot) slot) memory)
    state command).map (Option.map fun result =>
      (result.1, ((result.2.1.1, result.2.1.2.1, 8 + result.2.1.2.2), result.2.2)))

/-- The loaded command reads the stored physical family and history. -/
theorem gateSlotLoad_source (memory : Memory) (index : Nat) (slot : Fin 3) (state : SharedOracleSource)
    (represented : OracleFamilyMemory memory.ram state.family) (capacity : OracleFamilyFits state.family)
    (history : SharedHistoryMemory memory.ram state.metadata)
    (historyFits : ∀ selected, 256 + 2 * (recordHistoryPairs state.metadata.fixedTranscript selected).length < 2 ^ 110) :
    OracleFamilyMemory (executeLinear (gateSlotLoad index slot) memory).ram state.family ∧
      SharedHistoryMemory (executeLinear (gateSlotLoad index slot) memory).ram state.metadata := by
  refine ⟨OracleFamilyMemory.congr memory.ram _ state.family represented capacity
    (gateSlotLoad_public memory index slot), ?_⟩
  intro selected
  exact HistoryMemory.congr memory.ram _ _ _ (history selected) (historyFits selected)
    (gateSlotLoad_public memory index slot _ 3)

/-- The coupled slot has the exact loaded machine marginal. -/
theorem gateDriverSlotCoupledSamples_machine (attempts : Nat) (gate : GateCode) (slot : Fin 3)
    (memory : Memory) (state : SharedOracleSource) (command : SharedCommand)
    (represented : OracleFamilyMemory memory.ram state.family) (capacity : OracleFamilyFits state.family)
    (history : SharedHistoryMemory memory.ram state.metadata)
    (index : gate.oracle slot = (sharedPhysicalIndex (.inl command.1)).val)
    (operand : memory.ram 16 = historyWord command.2.1)
    (target : memory.ram (BitVec.ofNat 256 (17 + slot.val)) = historyWord command.2.2)
    (historyFits : ∀ selected, 256 + 2 * (recordHistoryPairs state.metadata.fixedTranscript selected).length < 2 ^ 110) :
    (gateDriverSlotCoupledSamples attempts gate slot memory state command).map
      (Option.map fun result => (result.1, result.2.1)) =
      (gateDriverSlotSamples attempts gate slot memory).map
        (fun result => if result.1 = 304 then none else some ((), result)) := by
  let loaded := executeLinear (gateSlotLoad (gate.oracle slot) slot) memory
  have load := gateSlotLoad_values (gate.oracle slot) slot memory
  have source := gateSlotLoad_source memory (gate.oracle slot) slot state represented capacity history historyFits
  have loadedIndex : loaded.registers 9 = BitVec.ofNat 256 (sharedPhysicalIndex (.inl command.1)).val :=
    load.2.1.trans (congrArg (BitVec.ofNat 256) index)
  have loadedTarget : loaded.ram 14 = historyWord command.2.2 := by rw [load.2.2.2.1, Function.update_self]; exact target
  have law := checkedSlotCoupledSamples_machine attempts loaded state command source.2 loadedIndex
    (load.1.trans operand) loadedTarget (historyFits command.1)
  let oracle := sharedPhysicalIndex (.inl command.1)
  have physicalIndex : loaded.registers 9 = BitVec.ofNat 256 oracle.castSucc.val := by
    rw [Fin.val_castSucc]
    exact loadedIndex
  have counts := checkedSlotCounts_eq loaded (sharedPhysicalIndex (.inl command.1)).castSucc
    (state.family.permutations (sharedPhysicalIndex (.inl command.1)))
    (source.1.permutations _) physicalIndex (capacity.base _) (capacity.overlay _)
  have historyCount := checkedSlotHistoryCount_eq loaded (sharedPhysicalIndex (.inl command.1)).castSucc
    (recordHistoryPairs state.metadata.fixedTranscript command.1).length physicalIndex (source.2 command.1).count
    (by have := historyFits command.1; omega)
  have automatic : checkedSlotAutomaticSamples attempts loaded =
      checkedSlotSamples attempts (state.family.permutations (sharedPhysicalIndex (.inl command.1))).base.used
        (state.family.permutations (sharedPhysicalIndex (.inl command.1))).overlay.length
        (recordHistoryPairs state.metadata.fixedTranscript command.1).length loaded := by
    simp only [checkedSlotAutomaticSamples, counts.1, counts.2, historyCount]
  rw [← automatic] at law
  have mapped := congrArg (PMF.map (Option.map fun result : Unit × (Fin 305 × Memory × Nat) =>
    (result.1, (result.2.1, result.2.2.1, 8 + result.2.2.2)))) law
  simp only [gateDriverSlotCoupledSamples, gateDriverSlotSamples, PMF.map_comp, Option.map_map, Function.comp_def]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def] at mapped
  rw [mapped]
  apply congrArg (fun f => PMF.map f (checkedSlotAutomaticSamples attempts loaded))
  funext result
  split <;> rfl

/-- The coupled slot has the exact typed shared programming marginal. -/
theorem gateDriverSlotCoupledSamples_source [BN254.FieldCertificate] (attempts : Nat) (gate : GateCode) (slot : Fin 3)
    (memory : Memory) (state : SharedOracleSource) (command : SharedCommand)
    (represented : OracleFamilyMemory memory.ram state.family) (capacity : OracleFamilyFits state.family)
    (index : gate.oracle slot = (sharedPhysicalIndex (.inl command.1)).val)
    (operand : memory.ram 16 = historyWord command.2.1)
    (baseRoom : 2 * ((state.family.permutations (sharedPhysicalIndex (.inl command.1))).base.used + 1) ≤ 2 ^ 110) :
    (gateDriverSlotCoupledSamples attempts gate slot memory state command).map
      (Option.map fun result => (result.1, result.2.2)) =
      sharedSourceCutoff attempts (.inl (.program command)) state := by
  have represented' := OracleFamilyMemory.congr memory.ram _ state.family represented capacity
    (gateSlotLoad_public memory (gate.oracle slot) slot)
  have load := gateSlotLoad_values (gate.oracle slot) slot memory
  simpa only [gateDriverSlotCoupledSamples, PMF.map_comp, Option.map_map, Function.comp_def] using
    checkedSlotCoupledSamples_source attempts (executeLinear (gateSlotLoad (gate.oracle slot) slot) memory)
      state command represented' capacity (load.2.1.trans (congrArg (BitVec.ofNat 256) index))
      (load.1.trans operand) baseRoom

/-- Every accepted loaded slot preserves the full source relation. -/
theorem gateDriverSlotCoupledSamples_preserves [BN254.FieldCertificate] (attempts : Nat) (gate : GateCode) (slot : Fin 3)
    (memory : Memory) (state : SharedOracleSource) (command : SharedCommand)
    (represented : OracleFamilyMemory memory.ram state.family) (capacity : OracleFamilyFits state.family)
    (history : SharedHistoryMemory memory.ram state.metadata)
    (index : gate.oracle slot = (sharedPhysicalIndex (.inl command.1)).val)
    (operand : memory.ram 16 = historyWord command.2.1)
    (target : memory.ram (BitVec.ofNat 256 (17 + slot.val)) = historyWord command.2.2)
    (historyFits : ∀ selected, 256 + 2 * (recordHistoryPairs state.metadata.fixedTranscript selected).length < 2 ^ 110)
    (baseRoom : 2 * ((state.family.permutations (sharedPhysicalIndex (.inl command.1))).base.used + 1) + 256 < 2 ^ 110)
    (overlayRoom : 256 + 2 * ((state.family.permutations (sharedPhysicalIndex (.inl command.1))).overlay.length + 1) < 2 ^ 110)
    (historyRoom : 256 + 2 * ((recordHistoryPairs state.metadata.fixedTranscript command.1).length + 1) < 2 ^ 110)
    (result : Fin 305 × Memory × Nat) (next : SharedOracleSource)
    (supported : some ((), (result, next)) ∈ (gateDriverSlotCoupledSamples attempts gate slot memory state command).support) :
    OracleFamilyMemory result.2.1.ram next.family ∧ OracleFamilyFits next.family ∧
      SharedHistoryMemory result.2.1.ram next.metadata := by
  obtain ⟨draw, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases draw with
  | none => simp at equal
  | some draw =>
    obtain ⟨value, actual, found⟩ := draw
    cases value
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at equal
    obtain ⟨resultEqual, rfl⟩ := equal
    subst result
    have load := gateSlotLoad_values (gate.oracle slot) slot memory
    have source := gateSlotLoad_source memory (gate.oracle slot) slot state represented capacity history historyFits
    have loadedTarget : (executeLinear (gateSlotLoad (gate.oracle slot) slot) memory).ram 14 = historyWord command.2.2 := by
      rw [load.2.2.2.1, Function.update_self]
      exact target
    exact checkedSlotCoupledSamples_preserves attempts _ state command source.1 capacity source.2
      (load.2.1.trans (congrArg (BitVec.ofNat 256) index)) (load.1.trans operand) loadedTarget
      baseRoom overlayRoom historyRoom historyFits actual found reached

end
end Kriterion.ArgoMAC.ArithmeticSimulator
