import Proof.Privacy.Simulator.Arithmetic.CheckedProgramMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section
set_option maxRecDepth 4096

/-- Every successful joint command retains the exact source family and shared transcript histories. -/
theorem checkedSlotJointSamples_preserves [BN254.FieldCertificate] (attempts : Nat) (memory : Memory)
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
    (supported : (result, some next) ∈ (checkedSlotJointSamples attempts memory state command).support) :
    OracleFamilyMemory result.2.1.ram next.family ∧ OracleFamilyFits next.family ∧
      SharedHistoryMemory result.2.1.ram next.metadata := by
  have machineSupport : result ∈ (checkedSlotSamples attempts
      (state.family.permutations (sharedPhysicalIndex (.inl command.1))).base.used
      (state.family.permutations (sharedPhysicalIndex (.inl command.1))).overlay.length
      (recordHistoryPairs state.metadata.fixedTranscript command.1).length memory).support := by
    rw [← checkedSlotJointSamples_machine attempts memory state command history index operand target (historyFits command.1)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(result, some next), supported, rfl⟩
  let oracle := sharedPhysicalIndex (.inl command.1)
  let pairs := recordHistoryPairs state.metadata.fixedTranscript command.1
  let prepared := checkedSlotPrepared pairs.length memory
  have preparedPublic : ∀ other region offset, offset < 2 ^ 110 →
      prepared.ram (oracleAddress other region offset) = memory.ram (oracleAddress other region offset) := by
    intro other region offset bound
    change (historyFreshSource pairs.length (executeLinear checkedSlotStart memory)).1.ram _ = _
    rw [(historyFreshSource_data pairs.length (executeLinear checkedSlotStart memory)).1]
    exact checkedSlotStart_public memory other region offset bound
  unfold checkedSlotJointSamples at supported
  split at supported
  · obtain ⟨⟨before, spent⟩, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    have outcome := congrArg Prod.snd equal
    have resultEqual := congrArg Prod.fst equal
    dsimp only at outcome resultEqual
    subst result
    cases observed : checkedProgramFamilyValue state.family oracle (blockFin command.2.1) (blockFin command.2.2) before with
    | none => simp only [show checkedProgramFamilyValue state.family (sharedPhysicalIndex (.inl command.1))
        (blockFin command.2.1) (blockFin command.2.2) before = none from observed, Option.map_none] at outcome
              contradiction
    | some family =>
      have nextEqual : (⟨family, state.metadata.program command⟩ : SharedOracleSource) = next := by
        simpa only [show checkedProgramFamilyValue state.family (sharedPhysicalIndex (.inl command.1))
          (blockFin command.2.1) (blockFin command.2.2) before = some family from observed, Option.map_some,
          Option.some.injEq] using outcome
      subst next
      have accepted : before.registers 7 ≠ 0 := by
        intro failed
        have failedWord : before.registers 7 = 0#256 := failed
        simp only [checkedProgramFamilyValue, overlayQueryValue, if_pos failedWord, Option.map_none] at observed
        contradiction
      let restored := checkedSlotRestored prepared
      have restoredFamily : OracleFamilyMemory restored.ram state.family :=
        OracleFamilyMemory.congr memory.ram restored.ram state.family represented capacity preparedPublic
      have restoredHistory : HistoryMemory restored.ram oracle.castSucc pairs :=
        HistoryMemory.congr memory.ram restored.ram oracle.castSucc pairs (history command.1) (historyFits command.1)
          (preparedPublic oracle.castSucc 3)
      have restoredIndex : restored.registers 9 = BitVec.ofNat 256 oracle.val :=
        (checkedSlotPreparedRestored_data memory pairs.length).1.trans index
      have restoredOperand : restored.registers 8 = BitVec.ofNat 256 (blockFin command.2.1).val :=
        (checkedSlotPreparedRestored_data memory pairs.length).2.1.trans operand
      have savedInput : restored.ram 26 = BitVec.ofNat 256 (blockFin command.2.1).val :=
        (checkedSlotPrepared_saved memory pairs.length).1.trans operand
      have savedTarget : restored.ram 28 = BitVec.ofNat 256 (blockFin command.2.2).val :=
        (checkedSlotPrepared_saved memory pairs.length).2.2.trans target
      obtain ⟨found, source, finalFamily, finalFits, finalHistory⟩ := checkedProgramAccepted_preserves attempts restored before spent
        state.family oracle (blockFin command.2.1) (blockFin command.2.2) pairs restoredFamily capacity restoredHistory
        restoredIndex restoredOperand savedInput savedTarget baseRoom overlayRoom historyRoom reached accepted
      have foundEqual : found = family := Option.some.inj (source.symm.trans observed)
      subst found
      refine ⟨finalFamily, finalFits, ?_⟩
      have selectedHistory : HistoryMemory
          (checkedSlotForwardResult (state.family.permutations oracle).overlay.length before).ram oracle.castSucc
          (pairs ++ [(historyWord command.2.1, historyWord command.2.2)]) := by
        simpa only [show ∀ value : Block, BitVec.ofNat 256 (blockFin value).val = historyWord value from fun _ => rfl] using finalHistory
      apply SharedHistoryMemory.program memory.ram _ state.metadata command history selectedHistory historyFits
      intro selected separate offset offsetFits
      have physicalIndex : memory.registers 9 = BitVec.ofNat 256 oracle.castSucc.val := by
        rw [Fin.val_castSucc]
        exact index
      exact checkedSlotSamples_otherHistory attempts pairs.length pairs.length memory oracle.castSucc
        (sharedPhysicalIndex (.inl selected)).castSucc (state.family.permutations oracle)
        (represented.permutations oracle) physicalIndex (history command.1).count (by dsimp only [oracle]; omega) (by dsimp only [oracle]; omega) (by dsimp only [pairs]; omega)
        (sharedFixedPhysical_ne separate) offset offsetFits _ machineSupport
  · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at supported
    obtain ⟨rfl, rfl⟩ := supported
    have finalPublic : ∀ other region offset, offset < 2 ^ 110 →
        (executeLinear checkedSlotCollision prepared).ram (oracleAddress other region offset) =
          memory.ram (oracleAddress other region offset) := by
      intro other region offset bound
      rw [checkedSlotCollision_ram]
      have apart : oracleAddress other region offset ≠ (31 : Word) :=
        oracleAddress_private_disjoint other region offset 31 bound (by decide)
      rw [Function.update_of_ne apart]
      exact preparedPublic other region offset bound
    refine ⟨OracleFamilyMemory.congr memory.ram _ state.family represented capacity finalPublic, capacity, ?_⟩
    intro selected
    exact HistoryMemory.congr memory.ram _ _ _ (history selected) (historyFits selected)
      (finalPublic (sharedPhysicalIndex (.inl selected)).castSucc 3)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
