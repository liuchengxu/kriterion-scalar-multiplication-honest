import Proof.Privacy.Simulator.Arithmetic.CheckedSlotOtherHistory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle
set_option maxRecDepth 2048

/-- The history append retains every private word. -/
theorem historyAppended_private (memory : Memory) (oracle : Fin 15749) (count cell : Nat)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (counter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 count)
    (capacity : 257 + 2 * count < 2 ^ 110) (privateBound : cell < 2 ^ 96) :
    (historyAppended memory).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  rcases publicHistoryResult_addresses memory oracle count header counter with ⟨selected, domain, range⟩
  rw [historyAppended_ram, range, domain, selected]
  simp only [Function.update_of_ne (Ne.symm (oracleAddress_private_disjoint oracle 3 0 cell (by decide) privateBound)),
    Function.update_of_ne (Ne.symm (oracleAddress_private_disjoint oracle 3 (257 + 2 * count) cell capacity privateBound)),
    Function.update_of_ne (Ne.symm (oracleAddress_private_disjoint oracle 3 (256 + 2 * count) cell (by omega) privateBound))]

/-- A private address differs from each specified scratch address. -/
theorem privateWord_ne (cell scratch : Nat) (privateBound : cell < 2 ^ 96)
    (small : scratch < 2 ^ 96) (separate : cell ≠ scratch) :
    BitVec.ofNat 256 cell ≠ BitVec.ofNat 256 scratch := by
  intro same
  have values := congrArg BitVec.toNat same
  simp only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_trans privateBound (by decide : 2 ^ 96 < 2 ^ 256)),
    Nat.mod_eq_of_lt (lt_trans small (by decide : 2 ^ 96 < 2 ^ 256))] at values
  exact separate values

/-- The target setup retains each private word except its target scratch cell. -/
theorem checkedSlotTarget_private (memory : Memory) (cell : Nat) (privateBound : cell < 2 ^ 96)
    (separate : cell ≠ 14) :
    (executeLinear checkedSlotTarget memory).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  rw [(checkedSlotTarget_values memory).1]
  exact Function.update_of_ne (privateWord_ne cell 14 privateBound (by decide) separate) _ _

/-- A successful finish retains each private word outside its target scratch cell. -/
theorem checkedSlotFinished_private (memory : Memory) (oracle : Fin 15749)
    (overlayCount historyCount : Nat) (header : memory.registers 6 = oracleAddress oracle 0 0)
    (overlayCounter : memory.ram (oracleAddress oracle 2 0) = BitVec.ofNat 256 overlayCount)
    (historyCounter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount)
    (overlayRoom : 257 + 2 * overlayCount < 2 ^ 110)
    (historyRoom : 257 + 2 * historyCount < 2 ^ 110)
    (cell : Nat) (privateBound : cell < 2 ^ 96) (notTarget : cell ≠ 14) :
    (checkedSlotFinished memory).ram (BitVec.ofNat 256 cell) =
      memory.ram (BitVec.ofNat 256 cell) := by
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
  rw [historyAppended_private ready oracle historyCount cell readyHeader readyCounter historyRoom privateBound,
    readyRam, overlayAppended_private prepared oracle overlayCount cell preparedHeader preparedCounter overlayRoom privateBound]
  exact checkedSlotTarget_private memory cell privateBound notTarget

/-- Every complete checked command retains the caller buffers and saved gate words. -/
theorem checkedSlotSamples_private (attempts count historyCount : Nat) (memory : Memory)
    (oracle : Fin 15749) (state : ProgrammedPermutation (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (historyCounter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount)
    (baseRoom : 2 * (state.base.used + 1) ≤ 2 ^ 110)
    (overlayRoom : 257 + 2 * state.overlay.length < 2 ^ 110)
    (historyRoom : 257 + 2 * historyCount < 2 ^ 110)
    (cell : Nat) (privateBound : cell < 2 ^ 96) (lower : 15 ≤ cell)
    (not26 : cell ≠ 26) (not27 : cell ≠ 27) (not28 : cell ≠ 28) (not31 : cell ≠ 31)
    (result : Fin 305 × Memory × Nat)
    (supported : result ∈ (checkedSlotSamples attempts state.base.used state.overlay.length count memory).support) :
    result.2.1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  obtain ⟨⟨label, final, cost⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  subst result
  let prepared := checkedSlotPrepared count memory
  have preparedPublic : ∀ selected region cell, cell < 2 ^ 110 →
      prepared.ram (oracleAddress selected region cell) = memory.ram (oracleAddress selected region cell) := by
    intro selected region cell bound
    change (historyFreshSource count (executeLinear checkedSlotStart memory)).1.ram _ = _
    rw [(historyFreshSource_data count (executeLinear checkedSlotStart memory)).1]
    exact checkedSlotStart_public memory selected region cell bound
  have preparedPrivate : prepared.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
    change (historyFreshSource count (executeLinear checkedSlotStart memory)).1.ram _ = _
    rw [(historyFreshSource_data count (executeLinear checkedSlotStart memory)).1]
    rw [checkedSlotStart_ram]
    have h26 : BitVec.ofNat 256 cell ≠ (26 : Word) := privateWord_ne cell 26 privateBound (by decide) not26
    have h27 : BitVec.ofNat 256 cell ≠ (27 : Word) := privateWord_ne cell 27 privateBound (by decide) not27
    have h28 : BitVec.ofNat 256 cell ≠ (28 : Word) := privateWord_ne cell 28 privateBound (by decide) not28
    simp only [Function.update_of_ne h26, Function.update_of_ne h27, Function.update_of_ne h28]
  change (label, final, cost) ∈ (checkedSlotBranchSamples attempts _ _ prepared).support at member
  unfold checkedSlotBranchSamples at member
  split at member
  · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl, rfl⟩ := member
    rw [checkedSlotCollision_ram]
    have h31 : BitVec.ofNat 256 cell ≠ (31 : Word) := privateWord_ne cell 31 privateBound (by decide) not31
    rw [Function.update_of_ne h31]
    exact preparedPrivate
  · obtain ⟨⟨before, spent⟩, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj equal |>.imp_right Prod.mk.inj
    let restored := checkedSlotRestored prepared
    have restoredIndex : restored.registers 9 = BitVec.ofNat 256 oracle.val :=
      (checkedSlotPreparedRestored_data memory count).1.trans index
    have restoredCounter : restored.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 state.base.used :=
      (preparedPublic oracle 0 0 (by decide)).trans represented.base.count
    have frame := storedForwardSamples_private attempts state.base.used restored before spent reached
      oracle cell (by omega) privateBound restoredIndex restoredCounter baseRoom
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
      exact (congrFun tailRam _).trans (frame.trans preparedPrivate)
    · simp only [checkedSlotForwardResult, if_neg failed]
      exact (checkedSlotFinished_private tail oracle state.overlay.length historyCount tailHeader
        tailOverlay tailHistory overlayRoom historyRoom cell privateBound (by omega)).trans
          ((congrFun tailRam _).trans (frame.trans preparedPrivate))

end Kriterion.ArgoMAC.ArithmeticSimulator
