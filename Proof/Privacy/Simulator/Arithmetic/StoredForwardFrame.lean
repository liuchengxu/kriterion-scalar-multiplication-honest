import Proof.Privacy.Simulator.Arithmetic.PermutationFrame
import Proof.Privacy.Simulator.Arithmetic.StoredForward
import Proof.Privacy.Simulator.Arithmetic.OverlayMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The sparse-query source preserves every private cell above its scratch range. -/
theorem permutationForwardSamples_private (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (permutationForwardSamples attempts count count memory).support)
    (oracle : Fin 15749) (cell : Nat) (lower : 8 ≤ cell) (privateBound : cell < 2 ^ 96)
    (inputBase : memory.registers 1 = oracleAddress oracle 0 (2 ^ 110 - 2 * count))
    (outputBase : memory.registers 3 = oracleAddress oracle 1 (2 ^ 110 - 2 * count))
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  have startFits : 2 ^ 110 - 2 * (count + 1) < 2 ^ 110 := by omega
  have endFits : 2 ^ 110 - 2 * (count + 1) + 1 < 2 ^ 110 := by omega
  apply permutationForwardSamples_other attempts count count memory final cost supported
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans privateBound (by decide : 2 ^ 96 < 2 ^ 256))] using lower
  · rw [inputBase, oracleAddress_prepend oracle 0 count fits]
    exact Ne.symm (oracleAddress_private_disjoint oracle 0 _ cell startFits privateBound)
  · rw [inputBase, oracleAddress_prepend oracle 0 count fits]
    change BitVec.ofNat 256 cell ≠ oracleAddress oracle 0 _ + BitVec.ofNat 256 1
    rw [oracleAddress_add]
    exact Ne.symm (oracleAddress_private_disjoint oracle 0 _ cell endFits privateBound)
  · rw [outputBase, oracleAddress_prepend oracle 1 count fits]
    exact Ne.symm (oracleAddress_private_disjoint oracle 1 _ cell startFits privateBound)
  · rw [outputBase, oracleAddress_prepend oracle 1 count fits]
    change BitVec.ofNat 256 cell ≠ oracleAddress oracle 1 _ + BitVec.ofNat 256 1
    rw [oracleAddress_add]
    exact Ne.symm (oracleAddress_private_disjoint oracle 1 _ cell endFits privateBound)

/-- The sparse-query source preserves the third public region used by the overlay. -/
theorem permutationForwardSamples_overlay (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (permutationForwardSamples attempts count count memory).support)
    (oracle : Fin 15749) (offset : Nat) (offsetFits : offset < 2 ^ 110)
    (inputBase : memory.registers 1 = oracleAddress oracle 0 (2 ^ 110 - 2 * count))
    (outputBase : memory.registers 3 = oracleAddress oracle 1 (2 ^ 110 - 2 * count))
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.ram (oracleAddress oracle 2 offset) = memory.ram (oracleAddress oracle 2 offset) := by
  have different : ∀ table : Fin 4, table ≠ 2 → ∀ target, target < 2 ^ 110 →
      oracleAddress oracle 2 offset ≠ oracleAddress oracle table target := by
    intro table apart target targetFits equal
    exact apart (oracleAddress_injective oracle oracle 2 table offset target offsetFits targetFits equal).2.1.symm
  apply permutationForwardSamples_other attempts count count memory final cost supported
  · rw [oracleAddress_value oracle 2 offset offsetFits]
    exact le_trans (by decide : 8 ≤ 2 ^ 128) (oracleCell_bounds oracle 2 offset offsetFits).1
  · rw [inputBase, oracleAddress_prepend oracle 0 count fits]
    exact different 0 (by decide) _ (by omega)
  · rw [inputBase, oracleAddress_prepend oracle 0 count fits]
    change _ ≠ oracleAddress oracle 0 _ + BitVec.ofNat 256 1
    rw [oracleAddress_add]
    exact different 0 (by decide) _ (by omega)
  · rw [outputBase, oracleAddress_prepend oracle 1 count fits]
    exact different 1 (by decide) _ (by omega)
  · rw [outputBase, oracleAddress_prepend oracle 1 count fits]
    change _ ≠ oracleAddress oracle 1 _ + BitVec.ofNat 256 1
    rw [oracleAddress_add]
    exact different 1 (by decide) _ (by omega)

/-- Every stored forward sample restores its header register and preserves all overlay cells. -/
theorem storedForwardSamples_overlayFrame (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (storedForwardSamples attempts count memory).support)
    (oracle : Fin 15749) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.registers 6 = oracleAddress oracle 0 0 ∧
    ∀ offset, offset < 2 ^ 110 → final.ram (oracleAddress oracle 2 offset) = memory.ram (oracleAddress oracle 2 offset) := by
  unfold storedForwardSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have inputBase := oracleLoaded_inputBase memory oracle count index counter (by omega)
  have outputBase := oracleLoaded_outputBase memory oracle count index counter (by omega)
  have saved := permutationForwardSamples_private attempts count (oracleLoaded memory) before spent member
    oracle 13 (by decide) (by decide) inputBase outputBase fits
  have header : before.ram 13 = oracleAddress oracle 0 0 := by
    have kept : before.ram 13 = (oracleLoaded memory).ram 13 := saved
    exact kept.trans ((oracleLoaded_query memory).2.2.2.trans (by rw [index, oracleHeader_address]))
  constructor
  · simpa [oracleCommitted] using header
  · intro offset offsetFits
    have retained := permutationForwardSamples_overlay attempts count (oracleLoaded memory) before spent member
      oracle offset offsetFits inputBase outputBase fits
    have separate : oracleAddress oracle 2 offset ≠ oracleAddress oracle 0 0 := by
      intro eq
      have same := (oracleAddress_injective oracle oracle 2 0 offset 0 offsetFits (by decide) eq).2.1
      contradiction
    change Function.update before.ram (before.ram 13) (before.registers 0) (oracleAddress oracle 2 offset) = _
    rw [header, Function.update_of_ne separate, retained]
    exact oracleLoadRam_public memory oracle 2 offset offsetFits

/-- The overlay count condition follows from the initial overlay memory relation. -/
theorem storedForwardSamples_overlayCount {size : Nat} (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (storedForwardSamples attempts count memory).support)
    (oracle : Fin 15749) (pairs : List (Fin size × Fin size))
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (overlay : OverlayMemory memory.ram oracle pairs) (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.ram (overlayHeader final) = BitVec.ofNat 256 pairs.length := by
  have retained := storedForwardSamples_overlayFrame attempts count memory final cost supported oracle index counter fits
  rw [overlayHeader_address final oracle retained.1, retained.2 0 (by decide), overlay.count]

end Kriterion.ArgoMAC.ArithmeticSimulator
