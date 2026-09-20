import Proof.Privacy.Simulator.Arithmetic.CheckedProgramSource
import Proof.Privacy.Simulator.Arithmetic.SharedHistoryProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle
noncomputable section
set_option maxRecDepth 2048

/-- Every accepted command's observed source matches its final RAM and appended history. -/
theorem checkedProgramAccepted_preserves [BN254.FieldCertificate]
    (attempts : Nat) (memory before : Memory) (spent : Nat) (state : SparseOracleFamily) (oracle : Fin 15748)
    (input target : Fin (2 ^ 128)) (pairs : List (Word × Word))
    (represented : OracleFamilyMemory memory.ram state) (fits : OracleFamilyFits state)
    (history : HistoryMemory memory.ram oracle.castSucc pairs)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (savedInput : memory.ram 26 = BitVec.ofNat 256 input.val)
    (savedTarget : memory.ram 28 = BitVec.ofNat 256 target.val)
    (baseRoom : 2 * ((state.permutations oracle).base.used + 1) + 256 < 2 ^ 110)
    (overlayRoom : 256 + 2 * ((state.permutations oracle).overlay.length + 1) < 2 ^ 110)
    (historyRoom : 256 + 2 * (pairs.length + 1) < 2 ^ 110)
    (supported : (before, spent) ∈ (storedForwardSamples attempts (state.permutations oracle).base.used memory).support)
    (accepted : before.registers 7 ≠ 0) :
    ∃ next : SparseOracleFamily,
      checkedProgramFamilyValue state oracle input target before = some next ∧
      OracleFamilyMemory (checkedSlotForwardResult (state.permutations oracle).overlay.length before).ram next ∧
      OracleFamilyFits next ∧
      HistoryMemory (checkedSlotForwardResult (state.permutations oracle).overlay.length before).ram oracle.castSucc
        (pairs ++ [(BitVec.ofNat 256 input.val, BitVec.ofNat 256 target.val)]) := by
  let tail := (internalForwardTail (state.permutations oracle).overlay.length before).1
  have queried : (tail, spent - 1 + (internalForwardTail (state.permutations oracle).overlay.length before).2) ∈
      (internalForwardSamples attempts (state.permutations oracle).base.used
        (state.permutations oracle).overlay.length memory).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨(before, spent), supported, rfl⟩
  let next := state.updatePermutation oracle (internalForwardMemoryState (state.permutations oracle) input tail)
  have nextFamily : OracleFamilyMemory tail.ram next :=
    internalForwardSamples_family attempts memory tail _ state oracle input represented fits index operand baseRoom queried
  have nextFits : OracleFamilyFits next := internalForwardFamily_fits state oracle input tail fits (by omega)
  have nextHistory : HistoryMemory tail.ram oracle.castSucc pairs :=
    internalForwardSamples_historyMemory attempts _ _ memory tail _ oracle.castSucc pairs queried
      history index (represented.permutations oracle).base.count (by omega) (by omega)
  have tailAccepted : tail.registers 7 ≠ 0#256 := by
    rw [(internalForwardTail_data (state.permutations oracle).overlay.length before).2.2]
    exact accepted
  obtain ⟨current, currentValue⟩ := internalForwardSamples_valueWitness attempts memory tail _ oracle.castSucc
    (state.permutations oracle) input (represented.permutations oracle) index operand
    (by omega) (fits.overlay oracle) queried tailAccepted
  have keptInput : tail.ram 26 = memory.ram 26 := internalForwardSamples_private attempts _ _ memory tail _ queried
    oracle.castSucc 26 (by decide) (by decide) index (represented.permutations oracle).base.count (by omega)
  have keptTarget : tail.ram 28 = memory.ram 28 := internalForwardSamples_private attempts _ _ memory tail _ queried
    oracle.castSucc 28 (by decide) (by decide) index (represented.permutations oracle).base.count (by omega)
  have nextRoom : 256 + 2 * ((next.permutations oracle).overlay.length + 1) < 2 ^ 110 := by
    simpa only [next, SparseOracleFamily.updatePermutation, Function.update_self,
      (internalForwardMemoryState_growth _ input tail).2] using overlayRoom
  have finalRelations := checkedSlotFinished_family_history tail next oracle current input target pairs nextFamily nextFits nextHistory
    (internalForwardSamples_header attempts _ _ memory tail _ queried oracle.castSucc index
      (represented.permutations oracle).base.count (by omega)) currentValue
    (keptInput.trans savedInput) (keptTarget.trans savedTarget) nextRoom historyRoom
  refine ⟨checkedSlotProgrammedState next oracle current target, ?_, ?_,
    checkedSlotProgrammedState_fits next oracle current target nextFits nextRoom, ?_⟩
  · have output : overlayQueryValue (state.permutations oracle).overlay.length before = some (BitVec.ofNat 256 current.val) := by
      rw [← internalForwardTail_value]
      change queryValue tail = _
      simp only [queryValue, if_neg tailAccepted, currentValue]
    simp only [checkedProgramFamilyValue, output, Option.map_some,
      sparseWordValue_encoded _ _ (by decide : 2 ^ 128 ≤ 2 ^ 256)]
    congr 1
    have recovered : internalForwardMemoryState (state.permutations oracle) input tail =
        programmedForwardNext (state.permutations oracle) input current := by
      simp only [internalForwardMemoryState, queryValue, if_neg tailAccepted, currentValue,
        Option.map_some, Option.getD_some, sparseWordValue_encoded _ _ (by decide : 2 ^ 128 ≤ 2 ^ 256)]
    simp only [checkedSlotProgrammedState, next, recovered, SparseOracleFamily.updatePermutation, Function.update_self,
      Function.update_idem, programmedAfterForward]
  · simpa only [checkedSlotForwardResult, if_neg accepted] using finalRelations.1
  · simpa only [checkedSlotForwardResult, if_neg accepted] using finalRelations.2

end
end Kriterion.ArgoMAC.ArithmeticSimulator
