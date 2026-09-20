import Proof.Privacy.Simulator.Arithmetic.OracleFamilyHistory
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicStable
import Proof.Privacy.Simulator.Arithmetic.InternalForwardGrowth

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- One public forward reply adds at most one base entry and retains every swap. -/
theorem programmedForwardMemoryState_growth (state : ProgrammedPermutation (2 ^ 128))
    (input : Fin (2 ^ 128)) (memory : Memory) :
    (programmedForwardMemoryState state input memory).base.used ≤ state.base.used + 1 ∧
    (programmedForwardMemoryState state input memory).overlay = state.overlay := by
  unfold programmedForwardMemoryState
  cases overlayQueryValue state.overlay.length memory with
  | none => exact ⟨Nat.le_succ _, rfl⟩
  | some word => exact programmedForwardNext_growth _ _ _

/-- One inverse reply adds at most one base entry and retains every swap. -/
theorem programmedInverseNext_growth (state : ProgrammedPermutation (2 ^ 128))
    (input output : Fin (2 ^ 128)) :
    (programmedInverseNext state input output).base.used ≤ state.base.used + 1 ∧
    (programmedInverseNext state input output).overlay = state.overlay :=
  ⟨sparseForwardNext_used state.base.reverse _ _, rfl⟩

/-- The inverse observer retains the same count bound after a cutoff. -/
theorem programmedInverseMemoryState_growth (state : ProgrammedPermutation (2 ^ 128))
    (input : Fin (2 ^ 128)) (memory : Memory) :
    (programmedInverseMemoryState state input memory).base.used ≤ state.base.used + 1 ∧
    (programmedInverseMemoryState state input memory).overlay = state.overlay := by
  unfold programmedInverseMemoryState
  cases queryValue memory with
  | none => exact ⟨Nat.le_succ _, rfl⟩
  | some word => exact programmedInverseNext_growth _ _ _

/-- The family capacity survives one selected base update with the same swaps. -/
theorem OracleFamilyFits.updateRead (state : SparseOracleFamily) (oracle : Fin 15748)
    (next : ProgrammedPermutation (2 ^ 128)) (capacity : OracleFamilyFits state)
    (growth : next.base.used ≤ (state.permutations oracle).base.used + 1)
    (overlay : next.overlay = (state.permutations oracle).overlay)
    (room : 2 * ((state.permutations oracle).base.used + 1) ≤ 2 ^ 110) :
    OracleFamilyFits (state.updatePermutation oracle next) := by
  constructor
  · intro index
    by_cases same : index = oracle
    · subst index
      simp only [SparseOracleFamily.updatePermutation, Function.update_self]
      exact (Nat.mul_le_mul_left 2 growth).trans room
    · simpa only [SparseOracleFamily.updatePermutation, Function.update_of_ne same] using capacity.base index
  · intro index
    by_cases same : index = oracle
    · subst index
      simpa only [SparseOracleFamily.updatePermutation, Function.update_self, overlay] using capacity.overlay oracle
    · simpa only [SparseOracleFamily.updatePermutation, Function.update_of_ne same] using capacity.overlay index
  · exact capacity.hash

/-- The recorded forward tail changes only the visible history and output stack. -/
theorem recordedPublicForwardTail_family (count : Nat) (memory : Memory) (state : SparseOracleFamily)
    (oracle : Fin 15749) (historyCount : Nat)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (history : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount)
    (room : 257 + 2 * historyCount < 2 ^ 110) :
    OracleFamilyMemory (recordedPublicForwardTail count memory).1.ram state := by
  unfold recordedPublicForwardTail
  split
  · exact represented
  · rw [wordOutput_ram]
    have scan := overlayForward_data count memory
    apply publicHistoryResult_family _ state oracle historyCount
    · rw [scan.1]
      exact represented
    · exact capacity
    · exact (scan.2.2 6 (by decide)).trans header
    · exact (congrFun scan.1 _).trans history
    · exact room

/-- The recorded inverse tail changes only the visible history and output stack. -/
theorem recordedPublicInverseTail_family (memory : Memory) (state : SparseOracleFamily)
    (oracle : Fin 15749) (historyCount : Nat)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (history : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount)
    (room : 257 + 2 * historyCount < 2 ^ 110) :
    OracleFamilyMemory (recordedPublicInverseTail memory).1.ram state := by
  unfold recordedPublicInverseTail
  split
  · exact represented
  · rw [wordOutput_ram]
    exact publicHistoryResult_family memory state oracle historyCount represented capacity header history room

/-- The complete recorded forward source preserves its exact recovered family. -/
theorem storedForwardSamples_recordedFamily [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (state : SparseOracleFamily)
    (oracle : Fin 15748) (input : Fin (2 ^ 128)) (historyCount : Nat)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (room : 2 * ((state.permutations oracle).base.used + 1) + 256 < 2 ^ 110)
    (history : memory.ram (oracleAddress oracle.castSucc 3 0) = BitVec.ofNat 256 historyCount)
    (historyRoom : 257 + 2 * historyCount < 2 ^ 110)
    (supported : (final, cost) ∈ (storedForwardSamples attempts (state.permutations oracle).base.used memory).support) :
    let next := state.updatePermutation oracle (programmedForwardMemoryState (state.permutations oracle) input final)
    OracleFamilyMemory (recordedPublicForwardTail (state.permutations oracle).overlay.length final).1.ram next ∧
      OracleFamilyFits next := by
  dsimp only
  have stored := storedForwardSamples_family attempts memory final cost state oracle input
    represented capacity index operand room supported
  rw [publicForwardTail_ram] at stored
  have growth := programmedForwardMemoryState_growth (state.permutations oracle) input final
  have fits := OracleFamilyFits.updateRead state oracle _ capacity growth.1 growth.2 (by omega)
  have frame := storedForwardSamples_historyFrame attempts (state.permutations oracle).base.used
    memory final cost supported oracle.castSucc index (represented.permutations oracle).base.count (by omega)
  exact ⟨recordedPublicForwardTail_family _ final _ oracle.castSucc historyCount stored fits
    frame.1 ((frame.2 0 (by decide)).trans history) historyRoom, fits⟩

/-- The complete recorded inverse source preserves its exact recovered family. -/
theorem storedInverseSamples_recordedFamily [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (state : SparseOracleFamily)
    (oracle : Fin 15748) (input : Fin (2 ^ 128)) (historyCount : Nat)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (room : 2 * ((state.permutations oracle).base.used + 1) + 256 < 2 ^ 110)
    (history : memory.ram (oracleAddress oracle.castSucc 3 0) = BitVec.ofNat 256 historyCount)
    (historyRoom : 257 + 2 * historyCount < 2 ^ 110)
    (supported : (final, cost) ∈ (storedInverseSamples attempts (state.permutations oracle).base.used
      (publicInversePrepared (state.permutations oracle).overlay.length memory)).support) :
    let next := state.updatePermutation oracle (programmedInverseMemoryState (state.permutations oracle) input final)
    OracleFamilyMemory (recordedPublicInverseTail final).1.ram next ∧ OracleFamilyFits next := by
  dsimp only
  have stored := storedInverseSamples_family attempts memory final cost state oracle input
    represented capacity index operand room supported
  rw [publicInverseTail_ram] at stored
  have growth := programmedInverseMemoryState_growth (state.permutations oracle) input final
  have fits := OracleFamilyFits.updateRead state oracle _ capacity growth.1 growth.2 (by omega)
  have preparedIndex := (publicInversePrepared_data (state.permutations oracle).overlay.length memory).2.trans index
  have preparedCount := (publicInversePrepared_public (state.permutations oracle).overlay.length memory
    oracle.castSucc 0 0 (by decide)).trans (represented.permutations oracle).base.count
  have header := storedInverseSamples_header attempts (state.permutations oracle).base.used _ final cost
    supported oracle.castSucc preparedIndex preparedCount (by omega)
  have frame := storedInverseSamples_historyFrame attempts (state.permutations oracle).base.used _ final cost
    supported oracle.castSucc preparedIndex preparedCount (by omega) 0 (by decide)
  have historyNext := frame.trans ((publicInversePrepared_public (state.permutations oracle).overlay.length memory
    oracle.castSucc 3 0 (by decide)).trans history)
  exact ⟨recordedPublicInverseTail_family final _ oracle.castSucc historyCount stored fits header historyNext historyRoom, fits⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
