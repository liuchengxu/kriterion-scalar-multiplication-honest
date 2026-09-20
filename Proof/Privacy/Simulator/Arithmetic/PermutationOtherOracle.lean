import Proof.Privacy.Simulator.Arithmetic.StoredForwardFrame
import Proof.Privacy.Simulator.Arithmetic.StoredInverseSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A base query preserves every cell of every other public oracle. -/
theorem permutationForwardSamples_otherOracle (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (permutationForwardSamples attempts count count memory).support)
    (oracle other : Fin 15749) (separate : other ≠ oracle) (inputRegion outputRegion table : Fin 4)
    (offset : Nat) (offsetFits : offset < 2 ^ 110)
    (inputBase : memory.registers 1 = oracleAddress oracle inputRegion (2 ^ 110 - 2 * count))
    (outputBase : memory.registers 3 = oracleAddress oracle outputRegion (2 ^ 110 - 2 * count))
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.ram (oracleAddress other table offset) = memory.ram (oracleAddress other table offset) := by
  have different : ∀ region target, target < 2 ^ 110 →
      oracleAddress other table offset ≠ oracleAddress oracle region target := by
    intro region target targetFits equal
    exact separate (oracleAddress_injective other oracle table region offset target offsetFits targetFits equal).1
  apply permutationForwardSamples_other attempts count count memory final cost supported
  · rw [oracleAddress_value other table offset offsetFits]
    exact le_trans (by decide : 8 ≤ 2 ^ 128) (oracleCell_bounds other table offset offsetFits).1
  · rw [inputBase, oracleAddress_prepend oracle inputRegion count fits]
    exact different inputRegion _ (by omega)
  · rw [inputBase, oracleAddress_prepend oracle inputRegion count fits]
    change _ ≠ oracleAddress oracle inputRegion _ + BitVec.ofNat 256 1
    rw [oracleAddress_add]
    exact different inputRegion _ (by omega)
  · rw [outputBase, oracleAddress_prepend oracle outputRegion count fits]
    exact different outputRegion _ (by omega)
  · rw [outputBase, oracleAddress_prepend oracle outputRegion count fits]
    change _ ≠ oracleAddress oracle outputRegion _ + BitVec.ofNat 256 1
    rw [oracleAddress_add]
    exact different outputRegion _ (by omega)

/-- A base query preserves the saved header in either table orientation. -/
theorem permutationForwardSamples_savedHeader (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (permutationForwardSamples attempts count count memory).support)
    (oracle : Fin 15749) (inputRegion outputRegion : Fin 4)
    (inputBase : memory.registers 1 = oracleAddress oracle inputRegion (2 ^ 110 - 2 * count))
    (outputBase : memory.registers 3 = oracleAddress oracle outputRegion (2 ^ 110 - 2 * count))
    (fits : 2 * (count + 1) ≤ 2 ^ 110) : final.ram 13 = memory.ram 13 := by
  have separate : ∀ region target, target < 2 ^ 110 →
      (13 : Word) ≠ oracleAddress oracle region target := by
    intro region target targetFits
    exact Ne.symm (oracleAddress_private_disjoint oracle region target 13 targetFits (by decide))
  apply permutationForwardSamples_other attempts count count memory final cost supported
  · decide
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

/-- A count commit preserves all cells in a different oracle. -/
theorem oracleCommitted_otherOracle (memory : Memory) (oracle other : Fin 15749)
    (separate : other ≠ oracle) (table : Fin 4) (offset : Nat) (fits : offset < 2 ^ 110)
    (header : memory.ram 13 = oracleAddress oracle 0 0) :
    (oracleCommitted memory).ram (oracleAddress other table offset) = memory.ram (oracleAddress other table offset) := by
  have different : oracleAddress other table offset ≠ oracleAddress oracle 0 0 := by
    intro equal
    exact separate (oracleAddress_injective other oracle table 0 offset 0 fits (by decide) equal).1
  change Function.update memory.ram (memory.ram 13) (memory.registers 0) _ = _
  rw [header, Function.update_of_ne different]

/-- The complete loaded forward handler preserves every other oracle. -/
theorem storedForwardSamples_otherOracle (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (storedForwardSamples attempts count memory).support)
    (oracle other : Fin 15749) (separate : other ≠ oracle) (table : Fin 4) (offset : Nat)
    (offsetFits : offset < 2 ^ 110) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.ram (oracleAddress other table offset) = memory.ram (oracleAddress other table offset) := by
  unfold storedForwardSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have inputBase := oracleLoaded_inputBase memory oracle count index counter (by omega)
  have outputBase := oracleLoaded_outputBase memory oracle count index counter (by omega)
  have saved := permutationForwardSamples_savedHeader attempts count (oracleLoaded memory) before spent member
    oracle 0 1 inputBase outputBase fits
  have header : before.ram 13 = oracleAddress oracle 0 0 :=
    saved.trans ((oracleLoaded_query memory).2.2.2.trans (by rw [index, oracleHeader_address]))
  rw [oracleCommitted_otherOracle before oracle other separate table offset offsetFits header,
    permutationForwardSamples_otherOracle attempts count (oracleLoaded memory) before spent member
      oracle other separate 0 1 table offset offsetFits inputBase outputBase fits]
  exact oracleLoadRam_public memory other table offset offsetFits

/-- The complete loaded inverse handler preserves every other oracle. -/
theorem storedInverseSamples_otherOracle (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (storedInverseSamples attempts count memory).support)
    (oracle other : Fin 15749) (separate : other ≠ oracle) (table : Fin 4) (offset : Nat)
    (offsetFits : offset < 2 ^ 110) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.ram (oracleAddress other table offset) = memory.ram (oracleAddress other table offset) := by
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
  have committed : (inverseCommitted before).ram = (oracleCommitted before).ram := by
    simp [inverseCommitted, oracleCommitted, metadataSwapped]
  rw [committed, oracleCommitted_otherOracle before oracle other separate table offset offsetFits header,
    permutationForwardSamples_otherOracle attempts count (inverseLoaded memory) before spent member
      oracle other separate 1 0 table offset offsetFits inputBase outputBase fits, metadata.1]
  exact oracleLoadRam_public memory other table offset offsetFits

end Kriterion.ArgoMAC.ArithmeticSimulator
