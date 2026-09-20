import Proof.Privacy.Simulator.Arithmetic.StoredInverseOverlay
import Proof.Privacy.Simulator.Arithmetic.InternalForwardSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The sparse-query source preserves the fourth public region used by the public history. -/
theorem permutationForwardSamples_history (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (permutationForwardSamples attempts count count memory).support)
    (oracle : Fin 15749) (offset : Nat) (offsetFits : offset < 2 ^ 110)
    (inputBase : memory.registers 1 = oracleAddress oracle 0 (2 ^ 110 - 2 * count))
    (outputBase : memory.registers 3 = oracleAddress oracle 1 (2 ^ 110 - 2 * count))
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.ram (oracleAddress oracle 3 offset) = memory.ram (oracleAddress oracle 3 offset) := by
  have different : ∀ table : Fin 4, table ≠ 3 → ∀ target, target < 2 ^ 110 →
      oracleAddress oracle 3 offset ≠ oracleAddress oracle table target := by
    intro table apart target targetFits equal
    exact apart (oracleAddress_injective oracle oracle 3 table offset target offsetFits targetFits equal).2.1.symm
  apply permutationForwardSamples_other attempts count count memory final cost supported
  · rw [oracleAddress_value oracle 3 offset offsetFits]
    exact le_trans (by decide : 8 ≤ 2 ^ 128) (oracleCell_bounds oracle 3 offset offsetFits).1
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

/-- Every stored forward sample restores its header register and preserves all public history cells. -/
theorem storedForwardSamples_historyFrame (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (storedForwardSamples attempts count memory).support)
    (oracle : Fin 15749) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.registers 6 = oracleAddress oracle 0 0 ∧
    ∀ offset, offset < 2 ^ 110 → final.ram (oracleAddress oracle 3 offset) = memory.ram (oracleAddress oracle 3 offset) := by
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
    have retained := permutationForwardSamples_history attempts count (oracleLoaded memory) before spent member
      oracle offset offsetFits inputBase outputBase fits
    have separate : oracleAddress oracle 3 offset ≠ oracleAddress oracle 0 0 := by
      intro eq
      have same := (oracleAddress_injective oracle oracle 3 0 offset 0 offsetFits (by decide) eq).2.1
      contradiction
    change Function.update before.ram (before.ram 13) (before.registers 0) (oracleAddress oracle 3 offset) = _
    rw [header, Function.update_of_ne separate, retained]
    exact oracleLoadRam_public memory oracle 3 offset offsetFits

/-- The sparse-query source preserves the fourth public region used by the public history. -/
theorem permutationForwardSamples_inverseHistory (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (permutationForwardSamples attempts count count memory).support)
    (oracle : Fin 15749) (offset : Nat) (offsetFits : offset < 2 ^ 110)
    (inputBase : memory.registers 1 = oracleAddress oracle 1 (2 ^ 110 - 2 * count))
    (outputBase : memory.registers 3 = oracleAddress oracle 0 (2 ^ 110 - 2 * count))
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.ram (oracleAddress oracle 3 offset) = memory.ram (oracleAddress oracle 3 offset) := by
  have different : ∀ table : Fin 4, table ≠ 3 → ∀ target, target < 2 ^ 110 →
      oracleAddress oracle 3 offset ≠ oracleAddress oracle table target := by
    intro table apart target targetFits equal
    exact apart (oracleAddress_injective oracle oracle 3 table offset target offsetFits targetFits equal).2.1.symm
  apply permutationForwardSamples_other attempts count count memory final cost supported
  · rw [oracleAddress_value oracle 3 offset offsetFits]
    exact le_trans (by decide : 8 ≤ 2 ^ 128) (oracleCell_bounds oracle 3 offset offsetFits).1
  · rw [inputBase, oracleAddress_prepend oracle 1 count fits]
    exact different 1 (by decide) _ (by omega)
  · rw [inputBase, oracleAddress_prepend oracle 1 count fits]
    change _ ≠ oracleAddress oracle 1 _ + BitVec.ofNat 256 1
    rw [oracleAddress_add]
    exact different 1 (by decide) _ (by omega)
  · rw [outputBase, oracleAddress_prepend oracle 0 count fits]
    exact different 0 (by decide) _ (by omega)
  · rw [outputBase, oracleAddress_prepend oracle 0 count fits]
    change _ ≠ oracleAddress oracle 0 _ + BitVec.ofNat 256 1
    rw [oracleAddress_add]
    exact different 0 (by decide) _ (by omega)

/-- The loaded inverse handler preserves its complete public history region. -/
theorem storedInverseSamples_historyFrame (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (storedInverseSamples attempts count memory).support)
    (oracle : Fin 15749) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    ∀ offset, offset < 2 ^ 110 → final.ram (oracleAddress oracle 3 offset) = memory.ram (oracleAddress oracle 3 offset) := by
  unfold storedInverseSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have metadata := inverseLoaded_metadata memory
  have inputBase := metadata.2.2.1.trans (oracleLoaded_outputBase memory oracle count index counter (by omega))
  have outputBase := metadata.2.2.2.1.trans (oracleLoaded_inputBase memory oracle count index counter (by omega))
  have saved := permutationForwardSamples_savedHeader attempts count (inverseLoaded memory) before spent member
    oracle 1 0 inputBase outputBase fits
  have header : before.ram 13 = oracleAddress oracle 0 0 :=
    saved.trans ((congrFun metadata.1 13).trans ((oracleLoaded_query memory).2.2.2.trans (by rw [index, oracleHeader_address])))
  intro offset offsetFits
  rw [inverseCommitted_ram]
  have separate : oracleAddress oracle 3 offset ≠ oracleAddress oracle 0 0 := by
    intro equal
    have same := (oracleAddress_injective oracle oracle 3 0 offset 0 offsetFits (by decide) equal).2.1
    contradiction
  change Function.update before.ram (before.ram 13) (before.registers 0) (oracleAddress oracle 3 offset) = _
  rw [header, Function.update_of_ne separate,
    permutationForwardSamples_inverseHistory attempts count (inverseLoaded memory) before spent member
      oracle offset offsetFits inputBase outputBase fits, metadata.1]
  exact oracleLoadRam_public memory oracle 3 offset offsetFits

/-- Every internal query preserves the complete external query and program history. -/
theorem internalForwardSamples_historyFrame (attempts count overlayCount : Nat)
    (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (internalForwardSamples attempts count overlayCount memory).support)
    (oracle : Fin 15749) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) (offset : Nat) (offsetFits : offset < 2 ^ 110) :
    final.ram (oracleAddress oracle 3 offset) = memory.ram (oracleAddress oracle 3 offset) := by
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  rw [(internalForwardTail_data overlayCount before).1]
  exact (storedForwardSamples_historyFrame attempts count memory before spent member
    oracle index counter fits).2 offset offsetFits

end Kriterion.ArgoMAC.ArithmeticSimulator
