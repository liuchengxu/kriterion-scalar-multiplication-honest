import Proof.Privacy.Simulator.Arithmetic.SharedHistorySource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle
open Security.SharedSimulatorMachine
noncomputable section

/-- The source appends the requested output swap after one forward query. -/
def programmedAfterForward (result : Fin (2 ^ 128) × ProgrammedPermutation (2 ^ 128))
    (target : Fin (2 ^ 128)) : ProgrammedPermutation (2 ^ 128) :=
  ⟨result.2.base, result.2.overlay ++ [(result.1, target)]⟩

/-- Programming has the exact law of a forward query followed by one output swap. -/
theorem programmed_program_forward (state : ProgrammedPermutation (2 ^ 128))
    (input target : Fin (2 ^ 128)) :
    state.program input target = (state.forward input).map (fun result => programmedAfterForward result target) := by
  unfold ProgrammedPermutation.program ProgrammedPermutation.forward
  cases state.base.forward input <;> rfl

/-- The stored query observer recovers the programmed family or its cutoff failure. -/
def checkedProgramFamilyValue (state : SparseOracleFamily) (oracle : Fin 15748)
    (input target : Fin (2 ^ 128)) (memory : Memory) : Option SparseOracleFamily :=
  (overlayQueryValue (state.permutations oracle).overlay.length memory).map fun word =>
    let current := sparseWordValue (2 ^ 128) (by decide) word
    state.updatePermutation oracle (programmedAfterForward
      (current, programmedForwardNext (state.permutations oracle) input current) target)

/-- The observed programmed family has the exact physical cutoff law. -/
theorem checkedProgramFamilyValue_law [BN254.FieldCertificate] (attempts : Nat) (memory : Memory)
    (state : SparseOracleFamily) (oracle : Fin 15748) (input target : Fin (2 ^ 128))
    (represented : OracleFamilyMemory memory.ram state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * ((state.permutations oracle).base.used + 1) ≤ 2 ^ 110)
    (overlayFits : 256 + 2 * (state.permutations oracle).overlay.length < 2 ^ 110) :
    (storedForwardSamples attempts (state.permutations oracle).base.used memory).map
      (fun result => checkedProgramFamilyValue state oracle input target result.1) =
      (drawCutoffLaw attempts ((state.permutations oracle).program input target)).map
        (Option.map (state.updatePermutation oracle)) := by
  have source := programmedForwardSamples_joint attempts memory oracle.castSucc (state.permutations oracle) input
    (represented.permutations oracle) index operand fits overlayFits
  have mapped := congrArg (PMF.map (Option.map fun result =>
    state.updatePermutation oracle (programmedAfterForward result target))) source
  rw [programmed_program_forward, drawCutoffLaw_map, PMF.map_comp]
  simpa only [PMF.map_comp, Function.comp_def, Option.map_map, checkedProgramFamilyValue] using mapped

/-- The joint command sample retains the actual machine result and the exact shared source result. -/
def checkedSlotJointSamples (attempts : Nat) (memory : Memory) (state : SharedOracleSource)
    (command : SharedCommand) : PMF ((Fin 305 × Memory × Nat) × Option SharedOracleSource) :=
  let oracle := sharedPhysicalIndex (.inl command.1)
  let permutation := state.family.permutations oracle
  let historyCount := (recordHistoryPairs state.metadata.fixedTranscript command.1).length
  let prepared := checkedSlotPrepared historyCount memory
  if freshPermutationPairCheck state.metadata.fixedTranscript command.1 command.2.1 command.2.2 then
    (storedForwardSamples attempts permutation.base.used (checkedSlotRestored prepared)).map fun result =>
      ((checkedSlotForwardReturn result.1, checkedSlotForwardResult permutation.overlay.length result.1,
        checkedSlotPrefixCost historyCount memory + (6 + checkedSlotForwardCost permutation.overlay.length result)),
       (checkedProgramFamilyValue state.family oracle (blockFin command.2.1) (blockFin command.2.2) result.1).map
         (fun family => (⟨family, state.metadata.program command⟩ : SharedOracleSource)))
  else PMF.pure ((300, executeLinear checkedSlotCollision prepared,
      checkedSlotPrefixCost historyCount memory + 4), some {state with metadata := state.metadata.markBad})

/-- The first joint marginal is the complete checked command's actual source. -/
theorem checkedSlotJointSamples_machine (attempts : Nat) (memory : Memory) (state : SharedOracleSource)
    (command : SharedCommand) (history : SharedHistoryMemory memory.ram state.metadata)
    (index : memory.registers 9 = BitVec.ofNat 256 (sharedPhysicalIndex (.inl command.1)).val)
    (operand : memory.registers 8 = historyWord command.2.1) (target : memory.ram 14 = historyWord command.2.2)
    (historyFits : 256 + 2 * (recordHistoryPairs state.metadata.fixedTranscript command.1).length < 2 ^ 110) :
    (checkedSlotJointSamples attempts memory state command).map Prod.fst =
      checkedSlotSamples attempts (state.family.permutations (sharedPhysicalIndex (.inl command.1))).base.used
        (state.family.permutations (sharedPhysicalIndex (.inl command.1))).overlay.length
        (recordHistoryPairs state.metadata.fixedTranscript command.1).length memory := by
  have accepted := checkedSlotPrepared_sharedFresh memory state.metadata command.1 command.2.1 command.2.2
    history index operand target historyFits
  by_cases fresh : freshPermutationPairCheck state.metadata.fixedTranscript command.1 command.2.1 command.2.2 = true
  · have good := accepted.mpr fresh
    simp only [checkedSlotJointSamples, if_pos fresh, checkedSlotSamples, checkedSlotBranchSamples, if_neg good,
      PMF.map_comp, Function.comp_def]
  · have collision : (checkedSlotPrepared (recordHistoryPairs state.metadata.fixedTranscript command.1).length memory).registers 7 = 0 := by
      by_contra different
      exact fresh (accepted.mp different)
    simp only [checkedSlotJointSamples, if_neg fresh, checkedSlotSamples, checkedSlotBranchSamples, if_pos collision,
      PMF.pure_map]

/-- The second joint marginal is the exact shared programmed source cutoff law. -/
theorem checkedSlotJointSamples_source [BN254.FieldCertificate] (attempts : Nat) (memory : Memory)
    (state : SharedOracleSource) (command : SharedCommand)
    (represented : OracleFamilyMemory memory.ram state.family) (capacity : OracleFamilyFits state.family)
    (index : memory.registers 9 = BitVec.ofNat 256 (sharedPhysicalIndex (.inl command.1)).val)
    (operand : memory.registers 8 = historyWord command.2.1)
    (baseRoom : 2 * ((state.family.permutations (sharedPhysicalIndex (.inl command.1))).base.used + 1) ≤ 2 ^ 110) :
    (checkedSlotJointSamples attempts memory state command).map Prod.snd =
      (drawCutoffLaw attempts (sharedInternalSourceDraw (.program command) state)).map (Option.map Prod.snd) := by
  let oracle := sharedPhysicalIndex (.inl command.1)
  let count := (recordHistoryPairs state.metadata.fixedTranscript command.1).length
  let restored := checkedSlotRestored (checkedSlotPrepared count memory)
  have stored : OracleFamilyMemory restored.ram state.family := by
    apply OracleFamilyMemory.congr memory.ram restored.ram state.family represented capacity
    intro other region offset bound
    rw [(checkedSlotPreparedRestored_data memory count).2.2]
    exact checkedSlotStart_public memory other region offset bound
  have restoredIndex : restored.registers 9 = BitVec.ofNat 256 oracle.val :=
    (checkedSlotPreparedRestored_data memory count).1.trans index
  have restoredOperand : restored.registers 8 = BitVec.ofNat 256 (blockFin command.2.1).val :=
    (checkedSlotPreparedRestored_data memory count).2.1.trans operand
  by_cases fresh : freshPermutationPairCheck state.metadata.fixedTranscript command.1 command.2.1 command.2.2 = true
  · have source := checkedProgramFamilyValue_law attempts restored state.family oracle (blockFin command.2.1)
      (blockFin command.2.2) stored restoredIndex restoredOperand baseRoom (capacity.overlay oracle)
    have mapped := congrArg (PMF.map (Option.map fun family =>
      (⟨family, state.metadata.program command⟩ : SharedOracleSource))) source
    simpa only [checkedSlotJointSamples, sharedInternalSourceDraw, if_pos fresh, physicalRequest, lowerRequest,
      oracleFamilyDraw, familyDraw, drawCutoffLaw_map, PMF.map_comp, Option.map_map, Function.comp_def,
      SparseOracleFamily.updatePermutation, oracle, restored, count] using mapped
  · simp only [checkedSlotJointSamples, sharedInternalSourceDraw, if_neg fresh, drawCutoffLaw, PMF.pure_map, Option.map_some]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
