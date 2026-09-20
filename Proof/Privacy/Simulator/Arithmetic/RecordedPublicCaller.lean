import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerHistory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine
noncomputable section

private theorem privateWord_ne (cell scratch : Nat) (lower : 51 ≤ cell)
    (upper : cell < 2 ^ 96) (small : scratch < 51) :
    BitVec.ofNat 256 cell ≠ BitVec.ofNat 256 scratch := by
  intro same
  have values := congrArg BitVec.toNat same
  have cellFits : cell < 2 ^ 256 := lt_trans upper (by decide)
  have scratchFits : scratch < 2 ^ 256 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt cellFits, Nat.mod_eq_of_lt scratchFits] at values
  omega

/-- The public reader preserves every private buffer word above its scratch cells. -/
theorem recordedPublicInputMemory_private (memory : Memory) (request : SharedQuery) (rest : List Bool)
    (cell : Nat) (lower : 51 ≤ cell) (upper : cell < 2 ^ 96) :
    (recordedPublicInputMemory memory request rest).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  rw [(recordedPublicInputMemory_values memory request rest).2.2.2.2]
  have separate49 : BitVec.ofNat 256 cell ≠ (49 : Word) := privateWord_ne cell 49 lower upper (by decide)
  have separate48 : BitVec.ofNat 256 cell ≠ (48 : Word) := privateWord_ne cell 48 lower upper (by decide)
  rw [Function.update_of_ne separate49, Function.update_of_ne separate48]

/-- The inverse reader preserves every private buffer word. -/
theorem publicInversePrepared_private (count : Nat) (memory : Memory)
    (cell : Nat) (lower : 51 ≤ cell) (upper : cell < 2 ^ 96) :
    (publicInversePrepared count memory).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  rw [(publicInversePrepared_data count memory).1]
  exact oracleLoadRam_private memory cell (by omega) upper

/-- A public history append cannot change a private buffer word. -/
theorem publicHistoryResult_private (memory : Memory) (oracle : Fin 15749) (count cell : Nat)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (counter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 count)
    (capacity : 257 + 2 * count < 2 ^ 110) (lower : 51 ≤ cell) (upper : cell < 2 ^ 96) :
    (publicHistoryResult memory).1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  rcases publicHistoryResult_addresses memory oracle count header counter with ⟨selected, domain, range⟩
  have headerSafe : historyHeader memory ≠ 50#256 := by
    rw [selected]
    exact oracleAddress_private_disjoint oracle 3 0 50 (by decide) (by decide)
  have scratchSafe := privateWord_ne cell 50 lower upper (by decide)
  have apart : ∀ target, target < 2 ^ 110 →
      BitVec.ofNat 256 cell ≠ oracleAddress oracle 3 target := by
    intro target fits
    exact (oracleAddress_private_disjoint oracle 3 target cell fits upper).symm
  rw [publicHistoryResult_ram memory headerSafe, range, domain, selected]
  split
  · rfl
  · split
    · simp only [Function.update_of_ne (apart 0 (by decide)),
        Function.update_of_ne (apart (256 + 2 * count) (by omega)),
        Function.update_of_ne (apart (257 + 2 * count) capacity)]
      exact Function.update_of_ne scratchSafe _ _
    · rfl

/-- The complete forward tail preserves each private buffer word. -/
theorem recordedPublicForwardTail_private (overlayCount : Nat) (memory : Memory)
    (oracle : Fin 15749) (historyCount cell : Nat)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (counter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount)
    (capacity : 257 + 2 * historyCount < 2 ^ 110) (lower : 51 ≤ cell) (upper : cell < 2 ^ 96) :
    (recordedPublicForwardTail overlayCount memory).1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  unfold recordedPublicForwardTail
  split
  · rfl
  · rw [wordOutput_ram]
    have scan := overlayForward_data overlayCount memory
    exact (publicHistoryResult_private _ oracle historyCount cell
      ((scan.2.2 6 (by decide)).trans header) ((congrFun scan.1 _).trans counter)
      capacity lower upper).trans (congrFun scan.1 _)

/-- The complete inverse tail preserves each private buffer word. -/
theorem recordedPublicInverseTail_private (memory : Memory) (oracle : Fin 15749) (historyCount cell : Nat)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (counter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount)
    (capacity : 257 + 2 * historyCount < 2 ^ 110) (lower : 51 ≤ cell) (upper : cell < 2 ^ 96) :
    (recordedPublicInverseTail memory).1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  unfold recordedPublicInverseTail
  split
  · rfl
  · rw [wordOutput_ram]
    exact publicHistoryResult_private memory oracle historyCount cell header counter capacity lower upper

/-- Every complete fixed forward query preserves the private buffers. -/
theorem storedForwardSamples_recordedPrivate (attempts count overlayCount : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (storedForwardSamples attempts count memory).support)
    (oracle : Fin 15749) (historyCount cell : Nat) (lower : 51 ≤ cell) (upper : cell < 2 ^ 96)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (history : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount)
    (room : 2 * (count + 1) ≤ 2 ^ 110) (historyRoom : 257 + 2 * historyCount < 2 ^ 110) :
    (recordedPublicForwardTail overlayCount final).1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  have frame := storedForwardSamples_historyFrame attempts count memory final cost supported oracle index counter room
  exact (recordedPublicForwardTail_private overlayCount final oracle historyCount cell frame.1
    ((frame.2 0 (by decide)).trans history) historyRoom lower upper).trans
    (storedForwardSamples_private attempts count memory final cost supported oracle cell (by omega) upper index counter room)

/-- Every complete fixed inverse query preserves the private buffers. -/
theorem storedInverseSamples_recordedPrivate (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (storedInverseSamples attempts count memory).support)
    (oracle : Fin 15749) (historyCount cell : Nat) (lower : 51 ≤ cell) (upper : cell < 2 ^ 96)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (history : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount)
    (room : 2 * (count + 1) ≤ 2 ^ 110) (historyRoom : 257 + 2 * historyCount < 2 ^ 110) :
    (recordedPublicInverseTail final).1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  have frame := storedInverseSamples_historyFrame attempts count memory final cost supported oracle index counter room
  have header := storedInverseSamples_header attempts count memory final cost supported oracle index counter room
  exact (recordedPublicInverseTail_private final oracle historyCount cell header
    ((frame 0 (by decide)).trans history) historyRoom lower upper).trans
    (storedInverseSamples_private attempts count memory final cost supported oracle cell (by omega) upper index counter room)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
