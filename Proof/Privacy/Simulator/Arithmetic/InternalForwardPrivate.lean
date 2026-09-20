import Proof.Privacy.Simulator.Arithmetic.InternalForwardSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The stored query preserves every caller cell above the reserved oracle scratch area. -/
theorem storedForwardSamples_privateFrame (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (storedForwardSamples attempts count memory).support)
    (oracle : Fin 15749) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * (count + 1) ≤ 2 ^ 110)
    (cell : Nat) (lower : 16 ≤ cell) (upper : cell < 2 ^ 96) :
    final.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  have header := (storedForwardSamples_overlayFrame attempts count memory final cost supported
    oracle index counter fits).1
  unfold storedForwardSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  change before.ram 13 = oracleAddress oracle 0 0 at header
  have kept := permutationForwardSamples_private attempts count (oracleLoaded memory) before spent member
    oracle cell (by omega) upper
    (oracleLoaded_inputBase memory oracle count index counter (by omega))
    (oracleLoaded_outputBase memory oracle count index counter (by omega)) fits
  have separate : BitVec.ofNat 256 cell ≠ oracleAddress oracle 0 0 :=
    (oracleAddress_private_disjoint oracle 0 0 cell (by decide) upper).symm
  change Function.update before.ram (before.ram 13) (before.registers 0) (BitVec.ofNat 256 cell) = _
  rw [header, Function.update_of_ne separate, kept]
  have different : ∀ scratch : Nat, scratch < 16 → BitVec.ofNat 256 cell ≠ BitVec.ofNat 256 scratch := by
    intro scratch small equal
    have same := congrArg BitVec.toNat equal
    have cellFits : cell < 2 ^ 256 := lt_trans upper (by decide)
    have scratchFits : scratch < 2 ^ 256 := by omega
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt cellFits, Nat.mod_eq_of_lt scratchFits] at same
    omega
  change oracleLoadRam memory (BitVec.ofNat 256 cell) = _
  have a : BitVec.ofNat 256 cell ≠ (13 : Word) := different 13 (by decide)
  have b : BitVec.ofNat 256 cell ≠ (12 : Word) := different 12 (by decide)
  have c : BitVec.ofNat 256 cell ≠ (9 : Word) := different 9 (by decide)
  simp only [oracleLoadRam, Function.update_of_ne a, Function.update_of_ne b, Function.update_of_ne c]

/-- Every accepted or rejected internal query preserves all caller private cells. -/
theorem internalForwardSamples_privateFrame (attempts count overlayCount : Nat)
    (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (internalForwardSamples attempts count overlayCount memory).support)
    (oracle : Fin 15749) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * (count + 1) ≤ 2 ^ 110)
    (cell : Nat) (lower : 16 ≤ cell) (upper : cell < 2 ^ 96) :
    final.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  rw [(internalForwardTail_data overlayCount before).1]
  exact storedForwardSamples_privateFrame attempts count memory before spent member oracle index counter fits cell lower upper

end Kriterion.ArgoMAC.ArithmeticSimulator
