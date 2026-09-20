import Proof.Privacy.Simulator.Arithmetic.CheckedSlotJointMemory
import Proof.Privacy.Simulator.Arithmetic.SharedSourceCutoff

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section

/-- The joint source fails exactly at the compiled slot's cutoff continuation. -/
theorem checkedSlotJointSamples_cutoff (attempts : Nat) (memory : Memory) (state : SharedOracleSource)
    (command : SharedCommand) (result : Fin 305 × Memory × Nat) (source : Option SharedOracleSource)
    (supported : (result, source) ∈ (checkedSlotJointSamples attempts memory state command).support) :
    source = none ↔ result.1 = 304 := by
  unfold checkedSlotJointSamples at supported
  split at supported
  · obtain ⟨⟨before, spent⟩, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    by_cases failed : before.registers 7 = 0#256
    · have failedNat : before.registers 7 = 0 := failed
      simp only [checkedProgramFamilyValue, overlayQueryValue, if_pos failed,
        Option.map_none, checkedSlotForwardReturn, if_pos failedNat]
    · have failedNat : before.registers 7 ≠ 0 := failed
      simp only [checkedProgramFamilyValue, overlayQueryValue, if_neg failed,
        Option.map_some, checkedSlotForwardReturn, if_neg failedNat]
      simp
  · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
    obtain ⟨rfl, rfl⟩ := supported
    simp

/-- The joint command treats only sampler cutoff as a failed source step. -/
def checkedSlotCoupledSamples (attempts : Nat) (memory : Memory) (state : SharedOracleSource)
    (command : SharedCommand) : PMF (Option (Unit × ((Fin 305 × Memory × Nat) × SharedOracleSource))) :=
  (checkedSlotJointSamples attempts memory state command).map fun result =>
    result.2.map fun next => ((), (result.1, next))

/-- The first coupled marginal retains the actual slot memory and instruction count. -/
theorem checkedSlotCoupledSamples_machine (attempts : Nat) (memory : Memory) (state : SharedOracleSource)
    (command : SharedCommand) (history : SharedHistoryMemory memory.ram state.metadata)
    (index : memory.registers 9 = BitVec.ofNat 256 (sharedPhysicalIndex (.inl command.1)).val)
    (operand : memory.registers 8 = historyWord command.2.1) (target : memory.ram 14 = historyWord command.2.2)
    (historyFits : 256 + 2 * (recordHistoryPairs state.metadata.fixedTranscript command.1).length < 2 ^ 110) :
    (checkedSlotCoupledSamples attempts memory state command).map (Option.map fun result => (result.1, result.2.1)) =
      (checkedSlotSamples attempts (state.family.permutations (sharedPhysicalIndex (.inl command.1))).base.used
        (state.family.permutations (sharedPhysicalIndex (.inl command.1))).overlay.length
        (recordHistoryPairs state.metadata.fixedTranscript command.1).length memory).map
          (fun result => if result.1 = 304 then none else some ((), result)) := by
  rw [← checkedSlotJointSamples_machine attempts memory state command history index operand target historyFits]
  simp only [checkedSlotCoupledSamples, PMF.map_comp, Function.comp_def]
  change (checkedSlotJointSamples attempts memory state command).bind _ = _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  have cutoff := checkedSlotJointSamples_cutoff attempts memory state command result.1 result.2 supported
  apply congrArg PMF.pure
  dsimp only
  cases source : result.2 with
  | none =>
      simp only [source, Option.map_none, if_pos (cutoff.mp source)]
  | some next =>
      have accepted : result.1.1 ≠ 304 := by intro failed; have := cutoff.mpr failed; simp [source] at this
      simp only [source, Option.map_some, if_neg accepted]

/-- The second coupled marginal is the exact shared source handler used by adaptive cutoff. -/
theorem checkedSlotCoupledSamples_source [BN254.FieldCertificate] (attempts : Nat) (memory : Memory)
    (state : SharedOracleSource) (command : SharedCommand)
    (represented : OracleFamilyMemory memory.ram state.family) (capacity : OracleFamilyFits state.family)
    (index : memory.registers 9 = BitVec.ofNat 256 (sharedPhysicalIndex (.inl command.1)).val)
    (operand : memory.registers 8 = historyWord command.2.1)
    (baseRoom : 2 * ((state.family.permutations (sharedPhysicalIndex (.inl command.1))).base.used + 1) ≤ 2 ^ 110) :
    (checkedSlotCoupledSamples attempts memory state command).map (Option.map fun result => (result.1, result.2.2)) =
      sharedSourceCutoff attempts (.inl (.program command)) state := by
  have source := checkedSlotJointSamples_source attempts memory state command represented capacity index operand baseRoom
  have paired := congrArg (PMF.map (Option.map fun next => ((), next))) source
  simp only [PMF.map_comp, Option.map_map, Function.comp_def] at paired
  change (checkedSlotCoupledSamples attempts memory state command).map _ =
    drawCutoffLaw attempts (sharedInternalSourceDraw (.program command) state)
  have identity : (drawCutoffLaw attempts (sharedInternalSourceDraw (.program command) state)).map
      (Option.map fun result => ((), result.2)) = drawCutoffLaw attempts (sharedInternalSourceDraw (.program command) state) := by
    have same : (fun result : Unit × SharedOracleSource => ((), result.2)) = id := by
      funext result; cases result with | mk unit source => cases unit; rfl
    rw [same]
    have sameOption : (Option.map (id : Unit × SharedOracleSource → Unit × SharedOracleSource)) = id := by
      funext result; cases result <;> rfl
    rw [sameOption]
    exact PMF.map_id _
  rw [← identity, ← paired]
  simp only [checkedSlotCoupledSamples, PMF.map_comp, Function.comp_def, Option.map_map]

/-- Every accepted coupled command preserves the exact source relation. -/
theorem checkedSlotCoupledSamples_preserves [BN254.FieldCertificate] (attempts : Nat) (memory : Memory)
    (state : SharedOracleSource) (command : SharedCommand)
    (represented : OracleFamilyMemory memory.ram state.family) (capacity : OracleFamilyFits state.family)
    (history : SharedHistoryMemory memory.ram state.metadata)
    (index : memory.registers 9 = BitVec.ofNat 256 (sharedPhysicalIndex (.inl command.1)).val)
    (operand : memory.registers 8 = historyWord command.2.1) (target : memory.ram 14 = historyWord command.2.2)
    (baseRoom : 2 * ((state.family.permutations (sharedPhysicalIndex (.inl command.1))).base.used + 1) + 256 < 2 ^ 110)
    (overlayRoom : 256 + 2 * ((state.family.permutations (sharedPhysicalIndex (.inl command.1))).overlay.length + 1) < 2 ^ 110)
    (historyRoom : 256 + 2 * ((recordHistoryPairs state.metadata.fixedTranscript command.1).length + 1) < 2 ^ 110)
    (historyFits : ∀ selected, 256 + 2 * (recordHistoryPairs state.metadata.fixedTranscript selected).length < 2 ^ 110)
    (result : Fin 305 × Memory × Nat) (next : SharedOracleSource)
    (supported : some ((), (result, next)) ∈ (checkedSlotCoupledSamples attempts memory state command).support) :
    OracleFamilyMemory result.2.1.ram next.family ∧ OracleFamilyFits next.family ∧
      SharedHistoryMemory result.2.1.ram next.metadata := by
  obtain ⟨⟨actual, source⟩, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases source with
  | none => simp at equal
  | some found =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at equal
    obtain ⟨rfl, rfl⟩ := equal
    exact checkedSlotJointSamples_preserves attempts memory state command represented capacity history
      index operand target baseRoom overlayRoom historyRoom historyFits actual found reached

end
end Kriterion.ArgoMAC.ArithmeticSimulator
