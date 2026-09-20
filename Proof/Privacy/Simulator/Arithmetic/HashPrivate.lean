import Proof.Privacy.Simulator.Arithmetic.HashOtherOracle

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The metadata loader preserves caller scratch and private RAM. -/
theorem oracleLoadRam_private (memory : Memory) (cell : Nat) (lower : 16 ≤ cell) (upper : cell < 2 ^ 96) :
    oracleLoadRam memory (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  have different : ∀ scratch : Nat, scratch < 16 → BitVec.ofNat 256 cell ≠ BitVec.ofNat 256 scratch := by
    intro scratch small equal
    have same := congrArg BitVec.toNat equal
    have cellFits : cell < 2 ^ 256 := lt_trans upper (by decide)
    have scratchFits : scratch < 2 ^ 256 := by omega
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt cellFits, Nat.mod_eq_of_lt scratchFits] at same
    omega
  have a : BitVec.ofNat 256 cell ≠ (13 : Word) := different 13 (by decide)
  have b : BitVec.ofNat 256 cell ≠ (12 : Word) := different 12 (by decide)
  have c : BitVec.ofNat 256 cell ≠ (9 : Word) := different 9 (by decide)
  simp only [oracleLoadRam, Function.update_of_ne a, Function.update_of_ne b, Function.update_of_ne c]

/-- Both hash tail paths preserve all caller private cells. -/
theorem hashTailSamples_private (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (hashTailSamples memory).support)
    (oracle : Fin 15749) (count cell : Nat) (upper : cell < 2 ^ 96)
    (base : memory.registers 5 = oracleAddress oracle 0 (2 ^ 110 - 2 * count))
    (header : memory.ram 13 = oracleAddress oracle 0 0)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  have separate : BitVec.ofNat 256 cell ≠ oracleAddress oracle 0 0 :=
    (oracleAddress_private_disjoint oracle 0 0 cell (by decide) upper).symm
  unfold hashTailSamples at supported
  split at supported
  · obtain ⟨value, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    have sampleBase : (frame memory value 0 0).registers 5 = oracleAddress oracle 0 (2 ^ 110 - 2 * count) := by
      simpa [frame] using base
    have saved := hashInstalled_private (frame memory value 0 0) oracle count 13 sampleBase fits (by decide)
    have committedHeader : (hashInstalled (frame memory value 0 0)).ram 13 = oracleAddress oracle 0 0 := saved.trans header
    change Function.update _ _ _ (BitVec.ofNat 256 cell) = _
    rw [committedHeader, Function.update_of_ne separate,
      hashInstalled_private (frame memory value 0 0) oracle count cell sampleBase fits upper]
    rfl
  · simp only [PMF.mem_support_pure_iff] at supported
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj supported
    change Function.update memory.ram (memory.ram 13) _ (BitVec.ofNat 256 cell) = _
    rw [header, Function.update_of_ne separate]

/-- Every hash sample preserves caller scratch and private RAM. -/
theorem hashHandlerSamples_private (count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (hashHandlerSamples count memory).support)
    (oracle : Fin 15749) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * (count + 1) ≤ 2 ^ 110)
    (cell : Nat) (lower : 16 ≤ cell) (upper : cell < 2 ^ 96) :
    final.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  unfold hashHandlerSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have scan := hashScan_frame count memory
  have base := scan.2.2.2.1.trans (oracleLoaded_inputBase memory oracle count index counter (by omega))
  have header : (hashScan count memory).1.ram 13 = oracleAddress oracle 0 0 := by
    rw [scan.1, (oracleLoaded_query memory).2.2.2, index, oracleHeader_address]
  rw [hashTailSamples_private _ before spent member oracle count cell upper base header fits, scan.1]
  exact oracleLoadRam_private memory cell lower upper

end Kriterion.ArgoMAC.ArithmeticSimulator
