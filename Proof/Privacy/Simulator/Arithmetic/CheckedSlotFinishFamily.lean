import Proof.Privacy.Simulator.Arithmetic.OracleFamilyHistory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle
set_option maxRecDepth 2048

/-- The target setup preserves every public cell. -/
theorem checkedSlotTarget_public (memory : Memory) (oracle : Fin 15749)
    (region : Fin 4) (offset : Nat) (fits : offset < 2 ^ 110) :
    (executeLinear checkedSlotTarget memory).ram (oracleAddress oracle region offset) =
      memory.ram (oracleAddress oracle region offset) := by
  rw [(checkedSlotTarget_values memory).1]
  exact Function.update_of_ne
    (oracleAddress_private_disjoint oracle region offset 14 fits (by decide)) _ _

/-- The overlay append retains every private word. -/
theorem overlayAppended_private (memory : Memory) (oracle : Fin 15749) (count address : Nat)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (counter : memory.ram (oracleAddress oracle 2 0) = BitVec.ofNat 256 count)
    (capacity : 257 + 2 * count < 2 ^ 110) (privateBound : address < 2 ^ 96) :
    (overlayAppended memory).ram (BitVec.ofNat 256 address) = memory.ram (BitVec.ofNat 256 address) := by
  have selected := overlayHeader_address memory oracle header
  have cursor : overlayHeader memory + (memory.ram (overlayHeader memory) * 2#256 + 256#256) =
      oracleAddress oracle 2 (256 + 2 * count) := by
    rw [selected, counter, ← BitVec.ofNat_mul, ← BitVec.ofNat_add, oracleAddress_add]
    congr 1
    omega
  have range : overlayHeader memory + (memory.ram (overlayHeader memory) * 2#256 + 256#256) + 1#256 =
      oracleAddress oracle 2 (257 + 2 * count) := by
    rw [cursor]
    change oracleAddress oracle 2 _ + BitVec.ofNat 256 1 = _
    rw [oracleAddress_add]
    congr 1
    omega
  rw [overlayAppended_ram, range, cursor, selected]
  simp only [Function.update_of_ne (Ne.symm (oracleAddress_private_disjoint oracle 2 0 address (by decide) privateBound)),
    Function.update_of_ne (Ne.symm (oracleAddress_private_disjoint oracle 2 (257 + 2 * count) address capacity privateBound)),
    Function.update_of_ne (Ne.symm (oracleAddress_private_disjoint oracle 2 (256 + 2 * count) address (by omega) privateBound))]

/-- One successful finish adds its swap to the selected source permutation. -/
def checkedSlotProgrammedState (state : SparseOracleFamily) (oracle : Fin 15748)
    (current target : Fin (2 ^ 128)) : SparseOracleFamily :=
  state.updatePermutation oracle ⟨(state.permutations oracle).base,
    (state.permutations oracle).overlay ++ [(current, target)]⟩

/-- The new overlay fits when its caller reserves one extra pair. -/
theorem checkedSlotProgrammedState_fits (state : SparseOracleFamily) (oracle : Fin 15748)
    (current target : Fin (2 ^ 128)) (fits : OracleFamilyFits state)
    (room : 256 + 2 * ((state.permutations oracle).overlay.length + 1) < 2 ^ 110) :
    OracleFamilyFits (checkedSlotProgrammedState state oracle current target) := by
  constructor
  · intro index
    by_cases same : index = oracle
    · subst index; simpa only [checkedSlotProgrammedState, SparseOracleFamily.updatePermutation, Function.update_self] using fits.base oracle
    · simpa only [checkedSlotProgrammedState, SparseOracleFamily.updatePermutation, Function.update_of_ne same] using fits.base index
  · intro index
    by_cases same : index = oracle
    · subst index; simpa only [checkedSlotProgrammedState, SparseOracleFamily.updatePermutation, Function.update_self,
        List.length_append, List.length_cons, List.length_nil, Nat.zero_add] using room
    · simpa only [checkedSlotProgrammedState, SparseOracleFamily.updatePermutation, Function.update_of_ne same] using fits.overlay index
  · exact fits.hash

/-- The successful finish preserves the full family and appends its exact requested history pair. -/
theorem checkedSlotFinished_family_history (memory : Memory) (state : SparseOracleFamily)
    (oracle : Fin 15748) (current input target : Fin (2 ^ 128)) (pairs : List (Word × Word))
    (represented : OracleFamilyMemory memory.ram state) (fits : OracleFamilyFits state)
    (history : HistoryMemory memory.ram oracle.castSucc pairs)
    (header : memory.registers 6 = oracleAddress oracle.castSucc 0 0)
    (answer : memory.registers 8 = BitVec.ofNat 256 current.val)
    (savedInput : memory.ram 26 = BitVec.ofNat 256 input.val)
    (savedTarget : memory.ram 28 = BitVec.ofNat 256 target.val)
    (overlayRoom : 256 + 2 * ((state.permutations oracle).overlay.length + 1) < 2 ^ 110)
    (historyRoom : 256 + 2 * (pairs.length + 1) < 2 ^ 110) :
    OracleFamilyMemory (checkedSlotFinished memory).ram (checkedSlotProgrammedState state oracle current target) ∧
      HistoryMemory (checkedSlotFinished memory).ram oracle.castSucc
        (pairs ++ [(BitVec.ofNat 256 input.val, BitVec.ofNat 256 target.val)]) := by
  let prepared := executeLinear checkedSlotTarget memory
  have preparedFamily : OracleFamilyMemory prepared.ram state :=
    OracleFamilyMemory.congr memory.ram prepared.ram state represented fits (checkedSlotTarget_public memory)
  have preparedHeader : prepared.registers 6 = oracleAddress oracle.castSucc 0 0 :=
    (checkedSlotTarget_values memory).2.1.trans header
  have preparedAnswer : prepared.registers 8 = BitVec.ofNat 256 current.val :=
    (checkedSlotTarget_values memory).2.2.1.trans answer
  have preparedTarget : prepared.ram 14 = BitVec.ofNat 256 target.val := by
    rw [(checkedSlotTarget_values memory).1, Function.update_self]
    exact savedTarget
  have overlayCounter := (preparedFamily.permutations oracle).overlay.count
  have overlayCap : 257 + 2 * (state.permutations oracle).overlay.length < 2 ^ 110 := by omega
  have appendedFamily : OracleFamilyMemory (overlayAppended prepared).ram
      (checkedSlotProgrammedState state oracle current target) := by
    apply OracleFamilyMemory.updatePermutation prepared.ram _ state oracle _ preparedFamily fits
    · constructor
      · exact overlayAppended_sparseMemory prepared oracle.castSucc _ _ (preparedFamily.permutations oracle).base
          preparedHeader overlayCounter (fits.base oracle) overlayCap
      · exact overlayAppended_memory prepared oracle.castSucc _ (preparedFamily.permutations oracle).overlay
          current target preparedHeader preparedAnswer preparedTarget (by omega)
    · intro other separate region offset bound
      exact overlayAppended_publicFrame prepared oracle.castSucc other _ preparedHeader overlayCounter overlayCap region offset bound (Or.inl separate)
  have preparedHistory : HistoryMemory prepared.ram oracle.castSucc pairs :=
    HistoryMemory.congr memory.ram prepared.ram oracle.castSucc pairs history (by omega)
      (checkedSlotTarget_public memory oracle.castSucc 3)
  have appendedHistory : HistoryMemory (overlayAppended prepared).ram oracle.castSucc pairs :=
    HistoryMemory.congr prepared.ram _ oracle.castSucc pairs preparedHistory (by omega)
      (fun offset bound => overlayAppended_publicFrame prepared oracle.castSucc oracle.castSucc _
        preparedHeader overlayCounter overlayCap 3 offset bound (Or.inr (by decide)))
  let ready := executeLinear checkedSlotHistory (overlayAppended prepared)
  have readyRam : ready.ram = (overlayAppended prepared).ram :=
    (checkedSlotHistory_values (overlayAppended prepared)).2.2.1
  have readyHeader : ready.registers 6 = oracleAddress oracle.castSucc 0 0 := by
    have same : ready.registers 6 = (overlayAppended prepared).registers 6 := by
      simp [ready, checkedSlotHistory, executeLinear, LinearInstruction.execute]
    exact same.trans ((overlayAppended_data prepared).2.1.trans preparedHeader)
  have readyInput : ready.registers 8 = BitVec.ofNat 256 input.val := by
    have kept : (overlayAppended prepared).ram 26 = prepared.ram 26 :=
      overlayAppended_private prepared oracle.castSucc _ 26 preparedHeader overlayCounter overlayCap (by decide)
    rw [(checkedSlotHistory_values (overlayAppended prepared)).1, kept]
    rw [(checkedSlotTarget_values memory).1, Function.update_of_ne (by decide : (26 : Word) ≠ 14)]
    exact savedInput
  have readyTarget : ready.registers 10 = BitVec.ofNat 256 target.val := by
    have kept : (overlayAppended prepared).ram 28 = prepared.ram 28 :=
      overlayAppended_private prepared oracle.castSucc _ 28 preparedHeader overlayCounter overlayCap (by decide)
    rw [(checkedSlotHistory_values (overlayAppended prepared)).2.1, kept]
    rw [(checkedSlotTarget_values memory).1, Function.update_of_ne (by decide : (28 : Word) ≠ 14)]
    exact savedTarget
  have readyFamily : OracleFamilyMemory ready.ram (checkedSlotProgrammedState state oracle current target) := by
    rw [readyRam]; exact appendedFamily
  have readyHistory : HistoryMemory ready.ram oracle.castSucc pairs := by rw [readyRam]; exact appendedHistory
  constructor
  · exact historyAppended_family ready _ oracle.castSucc pairs.length readyFamily
      (checkedSlotProgrammedState_fits state oracle current target fits overlayRoom)
      readyHeader readyHistory.count (by omega)
  · have result := historyAppended_memory ready oracle.castSucc pairs readyHistory readyHeader historyRoom
    rw [readyInput, readyTarget] at result
    exact result

end Kriterion.ArgoMAC.ArithmeticSimulator
