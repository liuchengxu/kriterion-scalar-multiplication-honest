import Proof.Privacy.Simulator.Arithmetic.HashQueryMemory
import Proof.Privacy.Simulator.Arithmetic.PermutationOtherOracle

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A fresh hash insertion preserves every cell of a different oracle. -/
theorem hashInstalled_otherOracle (memory : Memory) (oracle other : Fin 15749) (count : Nat)
    (separate : other ≠ oracle) (table : Fin 4) (offset : Nat) (offsetFits : offset < 2 ^ 110)
    (base : memory.registers 5 = oracleAddress oracle 0 (2 ^ 110 - 2 * count))
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    (hashInstalled memory).ram (oracleAddress other table offset) = memory.ram (oracleAddress other table offset) := by
  have address : memory.registers 5 - 2#256 = oracleAddress oracle 0 (2 ^ 110 - 2 * (count + 1)) := by
    rw [base, oracleAddress_prepend oracle 0 count fits]
  have different : ∀ target, target < 2 ^ 110 →
      oracleAddress other table offset ≠ oracleAddress oracle 0 target := by
    intro target targetFits equal
    exact separate (oracleAddress_injective other oracle table 0 offset target offsetFits targetFits equal).1
  have advance : oracleAddress oracle 0 (2 ^ 110 - 2 * (count + 1)) + 1#256 =
      oracleAddress oracle 0 (2 ^ 110 - 2 * (count + 1) + 1) := oracleAddress_add oracle 0 _ 1
  simp only [hashInstalled, address, advance, Function.update_of_ne (different (2 ^ 110 - 2 * (count + 1) + 1) (by omega)),
    Function.update_of_ne (different (2 ^ 110 - 2 * (count + 1)) (by omega))]

/-- Both hash tail paths preserve every cell of a different oracle. -/
theorem hashTailSamples_otherOracle (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (hashTailSamples memory).support)
    (oracle other : Fin 15749) (count : Nat) (separate : other ≠ oracle)
    (table : Fin 4) (offset : Nat) (offsetFits : offset < 2 ^ 110)
    (base : memory.registers 5 = oracleAddress oracle 0 (2 ^ 110 - 2 * count))
    (header : memory.ram 13 = oracleAddress oracle 0 0)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.ram (oracleAddress other table offset) = memory.ram (oracleAddress other table offset) := by
  unfold hashTailSamples at supported
  split at supported
  · obtain ⟨value, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    have sampleBase : (frame memory value 0 0).registers 5 = oracleAddress oracle 0 (2 ^ 110 - 2 * count) := by
      simpa [frame] using base
    have saved := hashInstalled_private (frame memory value 0 0) oracle count 13 sampleBase fits (by decide)
    have committedHeader : (hashInstalled (frame memory value 0 0)).ram 13 = oracleAddress oracle 0 0 := saved.trans header
    rw [oracleCommitted_otherOracle _ oracle other separate table offset offsetFits committedHeader]
    exact hashInstalled_otherOracle (frame memory value 0 0) oracle other count separate table offset offsetFits sampleBase fits
  · simp only [PMF.mem_support_pure_iff] at supported
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj supported
    exact oracleCommitted_otherOracle (hashFound memory) oracle other separate table offset offsetFits header

/-- The complete hash handler preserves every cell of every other oracle. -/
theorem hashHandlerSamples_otherOracle (count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (hashHandlerSamples count memory).support)
    (oracle other : Fin 15749) (separate : other ≠ oracle) (table : Fin 4) (offset : Nat)
    (offsetFits : offset < 2 ^ 110) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.ram (oracleAddress other table offset) = memory.ram (oracleAddress other table offset) := by
  unfold hashHandlerSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have frame := hashScan_frame count memory
  have base := frame.2.2.2.1.trans (oracleLoaded_inputBase memory oracle count index counter (by omega))
  have header : (hashScan count memory).1.ram 13 = oracleAddress oracle 0 0 := by
    rw [frame.1, (oracleLoaded_query memory).2.2.2, index, oracleHeader_address]
  rw [hashTailSamples_otherOracle _ before spent member oracle other count separate table offset offsetFits base header fits,
    frame.1]
  exact oracleLoadRam_public memory other table offset offsetFits

end Kriterion.ArgoMAC.ArithmeticSimulator
