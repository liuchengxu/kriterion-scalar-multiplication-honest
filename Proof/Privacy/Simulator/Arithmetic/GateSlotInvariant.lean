import Proof.Privacy.Simulator.Arithmetic.GateSlotCoupling
import Proof.Privacy.Simulator.Arithmetic.CheckedSlotCounts
import Proof.Privacy.Simulator.Arithmetic.CheckedSlotPrivate

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section
set_option maxRecDepth 4096

/-- The machine stores the exact source tables and all fixed histories. -/
structure SharedSourceMemory (memory : Memory) (state : SharedOracleSource) (limit : Nat) : Prop where
  family : OracleFamilyMemory memory.ram state.family
  capacity : OracleFamilyFits state.family
  history : SharedHistoryMemory memory.ram state.metadata
  counts : SharedSourceCounts state limit

/-- The slot reads its physical index and its two saved command words. -/
structure GateCommandMemory (gate : GateCode) (slot : Fin 3) (memory : Memory) (command : SharedCommand) : Prop where
  index : gate.oracle slot = (sharedPhysicalIndex (.inl command.1)).val
  operand : memory.ram 16 = historyWord command.2.1
  target : memory.ram (BitVec.ofNat 256 (17 + slot.val)) = historyWord command.2.2

/-- The represented source supplies every fixed history capacity. -/
theorem SharedSourceMemory.historyFits {memory : Memory} {state : SharedOracleSource} {limit : Nat}
    (represented : SharedSourceMemory memory state limit) (room : 256 + 2 * (limit + 1) < 2 ^ 110) :
    ∀ index, 256 + 2 * (recordHistoryPairs state.metadata.fixedTranscript index).length < 2 ^ 110 := by
  intro index
  have := represented.counts.2.2 index
  omega

/-- The exact loaded marginal recovers each accepted machine result. -/
theorem gateDriverSlotCoupledSamples_machineSupport (attempts limit : Nat) (gate : GateCode) (slot : Fin 3)
    (memory : Memory) (state : SharedOracleSource) (command : SharedCommand)
    (represented : SharedSourceMemory memory state limit) (stored : GateCommandMemory gate slot memory command)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) (result : Fin 305 × Memory × Nat) (next : SharedOracleSource)
    (supported : some ((), (result, next)) ∈ (gateDriverSlotCoupledSamples attempts gate slot memory state command).support) :
    result ∈ (gateDriverSlotSamples attempts gate slot memory).support ∧ result.1 ≠ 304 := by
  have projected : some ((), result) ∈ ((gateDriverSlotCoupledSamples attempts gate slot memory state command).map
      (Option.map fun outcome => (outcome.1, outcome.2.1))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨some ((), (result, next)), supported, rfl⟩
  rw [gateDriverSlotCoupledSamples_machine attempts gate slot memory state command represented.family represented.capacity
    represented.history stored.index stored.operand stored.target (represented.historyFits room)] at projected
  obtain ⟨actual, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp projected
  split at equal
  · contradiction
  · simp only [Option.some.injEq, Prod.mk.injEq, true_and] at equal
    subst result
    exact ⟨reached, by assumption⟩

/-- An accepted slot increases the exact source count cap by at most one. -/
theorem gateDriverSlotCoupledSamples_counts (attempts limit : Nat) (gate : GateCode) (slot : Fin 3)
    (memory : Memory) (state : SharedOracleSource) (command : SharedCommand)
    (bounded : SharedSourceCounts state limit) (result : Fin 305 × Memory × Nat) (next : SharedOracleSource)
    (supported : some ((), (result, next)) ∈ (gateDriverSlotCoupledSamples attempts gate slot memory state command).support) :
    SharedSourceCounts next (limit + 1) := by
  obtain ⟨draw, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases draw with
  | none => simp at equal
  | some draw =>
    obtain ⟨value, actual, found⟩ := draw
    cases value
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at equal
    obtain ⟨resultEqual, rfl⟩ := equal
    exact checkedSlotCoupledSamples_counts attempts limit _ state command bounded actual found reached

/-- An accepted slot preserves the represented source and its explicit count cap. -/
theorem gateDriverSlotCoupledSamples_memory [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode) (slot : Fin 3)
    (memory : Memory) (state : SharedOracleSource) (command : SharedCommand)
    (represented : SharedSourceMemory memory state limit) (stored : GateCommandMemory gate slot memory command)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) (result : Fin 305 × Memory × Nat) (next : SharedOracleSource)
    (supported : some ((), (result, next)) ∈ (gateDriverSlotCoupledSamples attempts gate slot memory state command).support) :
    SharedSourceMemory result.2.1 next (limit + 1) := by
  have base := represented.counts.1 (sharedPhysicalIndex (.inl command.1))
  have overlay := represented.counts.2.1 (sharedPhysicalIndex (.inl command.1))
  have history := represented.counts.2.2 command.1
  have preserved := gateDriverSlotCoupledSamples_preserves attempts gate slot memory state command
    represented.family represented.capacity represented.history stored.index stored.operand stored.target
    (represented.historyFits room) (by omega) (by omega) (by omega) result next supported
  exact ⟨preserved.1, preserved.2.1, preserved.2.2,
    gateDriverSlotCoupledSamples_counts attempts limit gate slot memory state command represented.counts result next supported⟩

/-- The source relation supplies the automatic loaded-slot reserve. -/
theorem gateDriverSlotReady_of_source (attempts limit : Nat) (gate : GateCode) (slot : Fin 3)
    (memory : Memory) (state : SharedOracleSource) (command : SharedCommand)
    (represented : SharedSourceMemory memory state limit) (stored : GateCommandMemory gate slot memory command)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) : GateDriverSlotReady attempts limit gate slot memory := by
  have source := gateSlotLoad_source memory (gate.oracle slot) slot state represented.family represented.capacity
    represented.history (represented.historyFits room)
  have load := gateSlotLoad_values (gate.oracle slot) slot memory
  have base := represented.counts.1 (sharedPhysicalIndex (.inl command.1))
  have overlay := represented.counts.2.1 (sharedPhysicalIndex (.inl command.1))
  have history := represented.counts.2.2 command.1
  exact checkedSlotReady_of_family attempts limit _ state.family (sharedPhysicalIndex (.inl command.1))
    (recordHistoryPairs state.metadata.fixedTranscript command.1).length source.1
    (load.2.1.trans (congrArg (BitVec.ofNat 256) stored.index)) (source.2 command.1).count
    (by omega) (by omega) (by omega) base overlay history

end
end Kriterion.ArgoMAC.ArithmeticSimulator
