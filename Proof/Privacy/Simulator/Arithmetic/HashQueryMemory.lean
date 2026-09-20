import Proof.Privacy.Simulator.Arithmetic.HashMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The lookup scan preserves every caller register below nine. -/
theorem tableScan_caller (count : Nat) (memory : Memory) (register : Register) (low : register.val < 9) :
    (tableScan count memory).1.registers register = memory.registers register := by
  have n9 : register ≠ 9 := by intro equal; subst register; norm_num at low
  have n10 : register ≠ 10 := by intro equal; subst register; norm_num at low
  have n11 : register ≠ 11 := by intro equal; subst register; norm_num at low
  have n12 : register ≠ 12 := by intro equal; subst register; norm_num at low
  have n13 : register ≠ 13 := by intro equal; subst register; norm_num at low
  induction count generalizing memory with
  | zero => simp [tableScan, n12]
  | succ count ih =>
      unfold tableScan
      split
      · simp [tableMatch, tableCompare, n9, n11, n12, n13]
      · rw [ih]
        simp [tableMiss, tableCompare, n9, n10, n13]

/-- The hash lookup retains its persistent RAM and required caller registers. -/
theorem hashScan_frame (count : Nat) (memory : Memory) :
    (hashScan count memory).1.ram = (oracleLoaded memory).ram ∧
    (hashScan count memory).1.registers 0 = (oracleLoaded memory).registers 0 ∧
    (hashScan count memory).1.registers 4 = (oracleLoaded memory).registers 4 ∧
    (hashScan count memory).1.registers 5 = (oracleLoaded memory).registers 1 ∧
    (hashScan count memory).1.registers 8 = (oracleLoaded memory).registers 8 := by
  refine ⟨(tableScan_data _ _).2, ?_, ?_, ?_, ?_⟩
  all_goals
    unfold hashScan
    rw [tableScan_caller _ _ _ (by decide)]
    simp [tableInitial, hashReady]

/-- Every sampled hash tail preserves the matching first-match source table. -/
theorem hashTailSamples_memory (memory final : Memory) (cost : Nat)
    (oracle : Fin 15749) (pairs : List (Word × Word))
    (represented : HashMemory memory.ram oracle pairs)
    (base : memory.registers 5 = oracleAddress oracle 0 (2 ^ 110 - 2 * pairs.length))
    (count : memory.registers 0 = BitVec.ofNat 256 pairs.length)
    (backupCount : memory.registers 4 = BitVec.ofNat 256 pairs.length)
    (header : memory.ram 13 = oracleAddress oracle 0 0)
    (fits : 2 * (pairs.length + 1) + 256 < 2 ^ 110)
    (supported : (final, cost) ∈ (hashTailSamples memory).support) :
    HashMemory final.ram oracle
      (if memory.registers 12 = 0#256 then (memory.registers 8, final.registers 8) :: pairs else pairs) := by
  unfold hashTailSamples at supported
  split at supported
  next fresh =>
    obtain ⟨value, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    rw [if_pos fresh]
    have inserted := hashInstalled_committed (frame memory value 0 0) oracle pairs represented.stored
      (by simpa [frame] using base) (by simpa [frame] using backupCount) header fits
    simpa [frame, oracleCommitted, hashInstalled] using inserted
  next known =>
    simp only [PMF.mem_support_pure_iff] at supported
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj supported
    rw [if_neg known]
    exact hashFound_committed memory oracle pairs represented count header (by omega)

end Kriterion.ArgoMAC.ArithmeticSimulator
