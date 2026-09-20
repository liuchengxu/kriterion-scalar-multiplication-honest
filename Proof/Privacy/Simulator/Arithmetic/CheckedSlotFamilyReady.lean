import Proof.Privacy.Simulator.Arithmetic.CheckedSlotAutomatic
import Proof.Privacy.Simulator.Arithmetic.OracleFamilyMemory
import Proof.Privacy.Simulator.Arithmetic.PublicHistoryResultPhysical

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle
set_option maxRecDepth 2048

/-- The command setup changes only its three private saved words. -/
theorem checkedSlotStart_ram (memory : Memory) :
    (executeLinear checkedSlotStart memory).ram =
      Function.update (Function.update (Function.update memory.ram 26 (memory.registers 8))
        27 (memory.registers 9)) 28 (memory.ram 14) := by
  simp [checkedSlotStart, executeLinear, LinearInstruction.execute]

/-- The command setup preserves every public table cell. -/
theorem checkedSlotStart_public (memory : Memory) (oracle : Fin 15749)
    (table : Fin 4) (offset : Nat) (fits : offset < 2 ^ 110) :
    (executeLinear checkedSlotStart memory).ram (oracleAddress oracle table offset) =
      memory.ram (oracleAddress oracle table offset) := by
  rw [checkedSlotStart_ram]
  have separate26 : oracleAddress oracle table offset ≠ (26 : Word) :=
    oracleAddress_private_disjoint oracle table offset 26 fits (by decide)
  have separate27 : oracleAddress oracle table offset ≠ (27 : Word) :=
    oracleAddress_private_disjoint oracle table offset 27 fits (by decide)
  have separate28 : oracleAddress oracle table offset ≠ (28 : Word) :=
    oracleAddress_private_disjoint oracle table offset 28 fits (by decide)
  simp only [Function.update_of_ne separate26, Function.update_of_ne separate27,
    Function.update_of_ne separate28]

/-- The freshness prefix restores the saved query and preserves public RAM. -/
theorem checkedSlotPreparedRestored_data (memory : Memory) (count : Nat) :
    (checkedSlotRestored (checkedSlotPrepared count memory)).registers 9 = memory.registers 9 ∧
    (checkedSlotRestored (checkedSlotPrepared count memory)).registers 8 = memory.registers 8 ∧
    (checkedSlotRestored (checkedSlotPrepared count memory)).ram =
      (executeLinear checkedSlotStart memory).ram := by
  have retained := (historyFreshSource_data count (executeLinear checkedSlotStart memory)).1
  have saved := checkedSlotStart_values memory
  change (checkedSlotPrepared count memory).ram = _ at retained
  simp only [checkedSlotRestored, Function.update_self,
    Function.update_of_ne (by decide : (9 : Register) ≠ 10),
    Function.update_of_ne (by decide : (8 : Register) ≠ 10),
    Function.update_of_ne (by decide : (8 : Register) ≠ 9)]
  exact ⟨(congrFun retained 27).trans saved.2.1, (congrFun retained 26).trans saved.1, retained⟩

/-- The checked command reads the exact physical history count. -/
theorem checkedSlotHistoryCount_eq (memory : Memory) (oracle : Fin 15749) (count : Nat)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 count)
    (fits : count < 2 ^ 256) : checkedSlotHistoryCount memory = count := by
  have header : (executeLinear checkedSlotStart memory).registers 6 = oracleAddress oracle 0 0 := by
    rw [(checkedSlotStart_values memory).2.2.2.1, index, oracleHeader_address]
  unfold checkedSlotHistoryCount
  rw [historyHeader_address _ oracle header, checkedSlotStart_public memory oracle 3 0 (by decide), counter]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

/-- The command prefix preserves the selected finite permutation. -/
theorem checkedSlotPreparedRestored_programmed (memory : Memory) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (count : Nat)
    (represented : ProgrammedMemory memory.ram oracle state)
    (fits : 2 * state.base.used ≤ 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110) :
    ProgrammedMemory (checkedSlotRestored (checkedSlotPrepared count memory)).ram oracle state := by
  apply ProgrammedMemory.congr memory.ram _ oracle state represented fits overlayFits
  intro table offset bound
  rw [(checkedSlotPreparedRestored_data memory count).2.2]
  exact checkedSlotStart_public memory oracle table offset bound

/-- The command reads the exact sparse count and overlay count. -/
theorem checkedSlotCounts_eq (memory : Memory) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (fits : 2 * state.base.used ≤ 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110) :
    checkedSlotUsedCount memory = state.base.used ∧ checkedSlotOverlayCount memory = state.overlay.length := by
  let restored := checkedSlotRestored (checkedSlotPrepared (checkedSlotHistoryCount memory) memory)
  have restoredIndex : restored.registers 9 = BitVec.ofNat 256 oracle.val :=
    (checkedSlotPreparedRestored_data memory _).1.trans index
  have retained := checkedSlotPreparedRestored_programmed memory oracle state (checkedSlotHistoryCount memory) represented fits overlayFits
  constructor
  · change ((oracleLoaded restored).registers 0).toNat = _
    rw [oracleLoaded_used restored oracle restoredIndex, retained.base.count]
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  · change ((oracleLoaded restored).ram (overlayHeader (oracleLoaded restored))).toNat = _
    rw [overlayHeader_address _ oracle (oracleLoaded_header restored oracle restoredIndex)]
    rw [show (oracleLoaded restored).ram = oracleLoadRam restored from rfl]
    rw [oracleLoadRam_public restored oracle 2 0 (by decide), retained.overlay.count]
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)

/-- A represented permutation supplies the automatic checked-command reserve. -/
theorem checkedSlotReady_of_programmed (attempts limit : Nat) (memory : Memory) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (historyCount : Nat)
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (history : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount)
    (fits : 2 * (state.base.used + 1) ≤ 2 ^ 110)
    (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110) (historyFits : historyCount < 2 ^ 256)
    (usedBound : state.base.used ≤ limit) (overlayBound : state.overlay.length ≤ limit)
    (historyBound : historyCount ≤ limit) : CheckedSlotReady attempts limit memory := by
  have counts := checkedSlotCounts_eq memory oracle state represented index (by omega) overlayFits
  refine ⟨?_, counts.1 ▸ usedBound, counts.2 ▸ overlayBound, ?_⟩
  · intro result supported
    rw [counts.1] at supported
    have retained := checkedSlotPreparedRestored_programmed memory oracle state (checkedSlotHistoryCount memory) represented (by omega) overlayFits
    have restoredIndex := (checkedSlotPreparedRestored_data memory (checkedSlotHistoryCount memory)).1.trans index
    have after := storedForwardSamples_overlayMemory attempts _ result.1 result.2 oracle state retained
      restoredIndex fits overlayFits supported
    rw [overlayHeader_address _ oracle after.1, after.2.count, counts.2]
  · rw [checkedSlotHistoryCount_eq memory oracle historyCount index history historyFits]
    exact historyBound

/-- The full family supplies readiness for each selected physical permutation. -/
theorem checkedSlotReady_of_family (attempts limit : Nat) (memory : Memory) (state : SparseOracleFamily)
    (oracle : Fin 15748) (historyCount : Nat) (represented : OracleFamilyMemory memory.ram state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (history : memory.ram (oracleAddress oracle.castSucc 3 0) = BitVec.ofNat 256 historyCount)
    (fits : 2 * ((state.permutations oracle).base.used + 1) ≤ 2 ^ 110)
    (overlayFits : 256 + 2 * (state.permutations oracle).overlay.length < 2 ^ 110)
    (historyFits : historyCount < 2 ^ 256)
    (usedBound : (state.permutations oracle).base.used ≤ limit)
    (overlayBound : (state.permutations oracle).overlay.length ≤ limit)
    (historyBound : historyCount ≤ limit) : CheckedSlotReady attempts limit memory :=
  checkedSlotReady_of_programmed attempts limit memory oracle.castSucc (state.permutations oracle)
    historyCount (represented.permutations oracle) index history fits overlayFits historyFits
    usedBound overlayBound historyBound

end Kriterion.ArgoMAC.ArithmeticSimulator
