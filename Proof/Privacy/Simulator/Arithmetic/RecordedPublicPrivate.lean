import Proof.Privacy.Simulator.Arithmetic.InternalForwardSaved
import Proof.Privacy.Simulator.Arithmetic.HashPrivate
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicFamily

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Either table orientation preserves private cells outside the query scratch range. -/
theorem permutationForwardSamples_privateRegions (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (permutationForwardSamples attempts count count memory).support)
    (oracle : Fin 15749) (inputRegion outputRegion : Fin 4) (cell : Nat)
    (lower : 8 ≤ cell) (privateBound : cell < 2 ^ 96)
    (inputBase : memory.registers 1 = oracleAddress oracle inputRegion (2 ^ 110 - 2 * count))
    (outputBase : memory.registers 3 = oracleAddress oracle outputRegion (2 ^ 110 - 2 * count))
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  have separate : ∀ region target, target < 2 ^ 110 →
      BitVec.ofNat 256 cell ≠ oracleAddress oracle region target := by
    intro region target targetFits
    exact Ne.symm (oracleAddress_private_disjoint oracle region target cell targetFits privateBound)
  apply permutationForwardSamples_other attempts count count memory final cost supported
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans privateBound (by decide : 2 ^ 96 < 2 ^ 256))] using lower
  · rw [inputBase, oracleAddress_prepend oracle inputRegion count fits]
    exact separate inputRegion _ (by omega)
  · rw [inputBase, oracleAddress_prepend oracle inputRegion count fits]
    change _ ≠ oracleAddress oracle inputRegion _ + BitVec.ofNat 256 1
    rw [oracleAddress_add]
    exact separate inputRegion _ (by omega)
  · rw [outputBase, oracleAddress_prepend oracle outputRegion count fits]
    exact separate outputRegion _ (by omega)
  · rw [outputBase, oracleAddress_prepend oracle outputRegion count fits]
    change _ ≠ oracleAddress oracle outputRegion _ + BitVec.ofNat 256 1
    rw [oracleAddress_add]
    exact separate outputRegion _ (by omega)

/-- A stored inverse query preserves caller words above its metadata scratch cells. -/
theorem storedInverseSamples_private (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (storedInverseSamples attempts count memory).support)
    (oracle : Fin 15749) (cell : Nat) (lower : 16 ≤ cell) (privateBound : cell < 2 ^ 96)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  unfold storedInverseSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have metadata := inverseLoaded_metadata memory
  have inputBase := metadata.2.2.1.trans (oracleLoaded_outputBase memory oracle count index counter (by omega))
  have outputBase := metadata.2.2.2.1.trans (oracleLoaded_inputBase memory oracle count index counter (by omega))
  have kept := permutationForwardSamples_privateRegions attempts count (inverseLoaded memory) before spent member
    oracle 1 0 cell (by omega) privateBound inputBase outputBase fits
  have saved := permutationForwardSamples_savedHeader attempts count (inverseLoaded memory) before spent member
    oracle 1 0 inputBase outputBase fits
  have header : before.ram 13 = oracleAddress oracle 0 0 :=
    saved.trans ((congrFun metadata.1 13).trans ((oracleLoaded_query memory).2.2.2.trans (by rw [index, oracleHeader_address])))
  change Function.update before.ram (before.ram 13) (before.registers 0) (BitVec.ofNat 256 cell) = _
  rw [header, Function.update_of_ne (Ne.symm (oracleAddress_private_disjoint oracle 0 0 cell (by decide) privateBound)), kept]
  rw [metadata.1]
  exact oracleLoadRam_private memory cell lower privateBound

end Kriterion.ArgoMAC.ArithmeticSimulator
