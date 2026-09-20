import Proof.Privacy.Simulator.Arithmetic.CheckedSlotPreservation

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle
set_option maxRecDepth 2048

/-- A successful finish preserves every other oracle's history region. -/
theorem checkedSlotFinished_otherHistory (memory : Memory) (oracle other : Fin 15749)
    (overlayCount historyCount : Nat) (header : memory.registers 6 = oracleAddress oracle 0 0)
    (overlayCounter : memory.ram (oracleAddress oracle 2 0) = BitVec.ofNat 256 overlayCount)
    (historyCounter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount)
    (overlayRoom : 257 + 2 * overlayCount < 2 ^ 110)
    (historyRoom : 257 + 2 * historyCount < 2 ^ 110)
    (separate : other ≠ oracle) (offset : Nat) (offsetFits : offset < 2 ^ 110) :
    (checkedSlotFinished memory).ram (oracleAddress other 3 offset) =
      memory.ram (oracleAddress other 3 offset) := by
  let prepared := executeLinear checkedSlotTarget memory
  have preparedHeader : prepared.registers 6 = oracleAddress oracle 0 0 :=
    (checkedSlotTarget_values memory).2.1.trans header
  have preparedCounter : prepared.ram (oracleAddress oracle 2 0) = BitVec.ofNat 256 overlayCount :=
    (checkedSlotTarget_public memory oracle 2 0 (by decide)).trans overlayCounter
  let ready := executeLinear checkedSlotHistory (overlayAppended prepared)
  have readyRam : ready.ram = (overlayAppended prepared).ram := (checkedSlotHistory_values _).2.2.1
  have readyHeader : ready.registers 6 = oracleAddress oracle 0 0 := by
    have same : ready.registers 6 = (overlayAppended prepared).registers 6 := by
      simp [ready, checkedSlotHistory, executeLinear, LinearInstruction.execute]
    exact same.trans ((overlayAppended_data prepared).2.1.trans preparedHeader)
  have readyCounter : ready.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount := by
    rw [readyRam, overlayAppended_publicFrame prepared oracle oracle overlayCount preparedHeader preparedCounter
      overlayRoom 3 0 (by decide) (Or.inr (by decide)), checkedSlotTarget_public memory oracle 3 0 (by decide)]
    exact historyCounter
  change (historyAppended ready).ram _ = _
  rw [historyAppended_publicFrame ready oracle other historyCount readyHeader readyCounter historyRoom 3 offset offsetFits (Or.inl separate),
    readyRam, overlayAppended_publicFrame prepared oracle other overlayCount preparedHeader preparedCounter overlayRoom 3 offset offsetFits (Or.inl separate)]
  exact checkedSlotTarget_public memory other 3 offset offsetFits

/-- Every complete checked command preserves all other history regions. -/
theorem checkedSlotSamples_otherHistory (attempts count historyCount : Nat) (memory : Memory)
    (oracle other : Fin 15749) (state : ProgrammedPermutation (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (historyCounter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount)
    (baseRoom : 2 * (state.base.used + 1) ≤ 2 ^ 110)
    (overlayRoom : 257 + 2 * state.overlay.length < 2 ^ 110)
    (historyRoom : 257 + 2 * historyCount < 2 ^ 110)
    (separate : other ≠ oracle) (offset : Nat) (offsetFits : offset < 2 ^ 110)
    (result : Fin 305 × Memory × Nat)
    (supported : result ∈ (checkedSlotSamples attempts state.base.used state.overlay.length count memory).support) :
    result.2.1.ram (oracleAddress other 3 offset) = memory.ram (oracleAddress other 3 offset) := by
  obtain ⟨⟨label, final, cost⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  subst result
  let prepared := checkedSlotPrepared count memory
  have preparedPublic : ∀ selected region cell, cell < 2 ^ 110 →
      prepared.ram (oracleAddress selected region cell) = memory.ram (oracleAddress selected region cell) := by
    intro selected region cell bound
    change (historyFreshSource count (executeLinear checkedSlotStart memory)).1.ram _ = _
    rw [(historyFreshSource_data count (executeLinear checkedSlotStart memory)).1]
    exact checkedSlotStart_public memory selected region cell bound
  change (label, final, cost) ∈ (checkedSlotBranchSamples attempts _ _ prepared).support at member
  unfold checkedSlotBranchSamples at member
  split at member
  · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl, rfl⟩ := member
    rw [checkedSlotCollision_ram]
    have apart : oracleAddress other 3 offset ≠ (31 : Word) :=
      oracleAddress_private_disjoint other 3 offset 31 offsetFits (by decide)
    rw [Function.update_of_ne apart]
    exact preparedPublic other 3 offset offsetFits
  · obtain ⟨⟨before, spent⟩, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj equal |>.imp_right Prod.mk.inj
    let restored := checkedSlotRestored prepared
    have restoredIndex : restored.registers 9 = BitVec.ofNat 256 oracle.val :=
      (checkedSlotPreparedRestored_data memory count).1.trans index
    have restoredCounter : restored.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 state.base.used :=
      (preparedPublic oracle 0 0 (by decide)).trans represented.base.count
    have frame := storedForwardSamples_otherOracle attempts state.base.used restored before spent reached
      oracle other separate 3 offset offsetFits restoredIndex restoredCounter baseRoom
    have selected := storedForwardSamples_historyFrame attempts state.base.used restored before spent reached
      oracle restoredIndex restoredCounter baseRoom
    have overlay := storedForwardSamples_overlayFrame attempts state.base.used restored before spent reached
      oracle restoredIndex restoredCounter baseRoom
    let tail := (internalForwardTail state.overlay.length before).1
    have tailRam : tail.ram = before.ram := (internalForwardTail_data _ before).1
    have tailHeader : tail.registers 6 = oracleAddress oracle 0 0 := by
      unfold tail internalForwardTail
      split
      · exact selected.1
      · exact ((overlayForward_data _ before).2.2 6 (by decide)).trans selected.1
    have tailOverlay : tail.ram (oracleAddress oracle 2 0) = BitVec.ofNat 256 state.overlay.length := by
      rw [tailRam, overlay.2 0 (by decide)]
      exact (preparedPublic oracle 2 0 (by decide)).trans represented.overlay.count
    have tailHistory : tail.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount := by
      rw [tailRam, selected.2 0 (by decide)]
      exact (preparedPublic oracle 3 0 (by decide)).trans historyCounter
    by_cases failed : before.registers 7 = 0
    · simp only [checkedSlotForwardResult, if_pos failed]
      exact (congrFun tailRam _).trans (frame.trans (preparedPublic other 3 offset offsetFits))
    · simp only [checkedSlotForwardResult, if_neg failed]
      exact (checkedSlotFinished_otherHistory tail oracle other state.overlay.length historyCount tailHeader
        tailOverlay tailHistory overlayRoom historyRoom separate offset offsetFits).trans
          ((congrFun tailRam _).trans (frame.trans (preparedPublic other 3 offset offsetFits)))

end Kriterion.ArgoMAC.ArithmeticSimulator
