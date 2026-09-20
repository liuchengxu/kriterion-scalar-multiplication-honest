import Proof.Privacy.Simulator.Arithmetic.SparseMemory
import Proof.Privacy.Simulator.Arithmetic.OverlayScan

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The overlay count and ascending swap list occupy the third public region. -/
structure OverlayMemory {size : Nat} (ram : Word → Word) (oracle : Fin 15749)
    (pairs : List (Fin size × Fin size)) : Prop where
  count : ram (oracleAddress oracle 2 0) = BitVec.ofNat 256 pairs.length
  stored : RepresentsPairs ram (oracleAddress oracle 2 256) (sparseWordPairs pairs)

/-- The overlay loader selects the third region from the base header. -/
theorem overlayHeader_address (memory : Memory) (oracle : Fin 15749)
    (header : memory.registers 6 = oracleAddress oracle 0 0) :
    overlayHeader memory = oracleAddress oracle 2 0 := by
  simp [overlayHeader, header, oracleAddress, oracleCell, BitVec.ofNat_add]

/-- The ascending overlay base follows its count header by 256 cells. -/
theorem overlayBase_address (memory : Memory) (oracle : Fin 15749)
    (header : memory.registers 6 = oracleAddress oracle 0 0) :
    overlayHeader memory + 256#256 = oracleAddress oracle 2 256 := by
  rw [overlayHeader_address memory oracle header]
  exact oracleAddress_add oracle 2 0 256

/-- Every occupied overlay pair lies above its count header. -/
theorem overlayPairs_header_disjoint (oracle : Fin 15749) (count index : Nat)
    (fits : 2 * count + 256 < 2 ^ 110) (inside : index < 2 * count) :
    oracleAddress oracle 2 256 + BitVec.ofNat 256 index ≠ oracleAddress oracle 2 0 := by
  rw [oracleAddress_add]
  intro equal
  have offsets := (oracleAddress_injective oracle oracle 2 2 _ 0 (by omega) (by decide) equal).2.2
  omega

/-- Overlay programming appends the source swap and persists the new count. -/
theorem overlayAppended_memory {size : Nat} (memory : Memory) (oracle : Fin 15749)
    (pairs : List (Fin size × Fin size)) (represented : OverlayMemory memory.ram oracle pairs)
    (current target : Fin size) (header : memory.registers 6 = oracleAddress oracle 0 0)
    (currentValue : memory.registers 8 = BitVec.ofNat 256 current.val)
    (targetValue : memory.ram 14 = BitVec.ofNat 256 target.val)
    (fits : 2 * (pairs.length + 1) + 256 < 2 ^ 110) :
    OverlayMemory (overlayAppended memory).ram oracle (pairs ++ [(current, target)]) := by
  have sourceHeader := overlayHeader_address memory oracle header
  have sourceBase := overlayBase_address memory oracle header
  have count : memory.ram (overlayHeader memory) = BitVec.ofNat 256 (sparseWordPairs pairs).length := by
    simpa only [sourceHeader, sparseWordPairs, List.length_map] using represented.count
  refine ⟨?_, ?_⟩
  · rw [← sourceHeader, overlayAppended_count]
    simpa [sourceHeader, represented.count, List.length_append, BitVec.ofNat_add]
  · have bound : 2 * (sparseWordPairs pairs).length + 2 ≤ 2 ^ 256 := by
      have large : 2 ^ 110 < 2 ^ 256 := by decide
      simp only [sparseWordPairs, List.length_map]
      omega
    have installed := overlayAppended_represents memory (sparseWordPairs pairs) count
      (by simpa only [sourceBase] using represented.stored) bound
      (by intro index inside; rw [sourceBase, sourceHeader]
          exact overlayPairs_header_disjoint oracle (pairs.length + 1) index fits
            (by simpa [sparseWordPairs] using inside))
    simpa only [sourceBase, currentValue, targetValue, sparseWordPairs, List.map_append,
      List.map_cons, List.map_nil] using installed

/-- The forward overlay scan returns the encoded source permutation value. -/
theorem overlayForward_encoded {size : Nat} (memory : Memory) (oracle : Fin 15749)
    (pairs : List (Fin size × Fin size)) (represented : OverlayMemory memory.ram oracle pairs)
    (value : Fin size) (header : memory.registers 6 = oracleAddress oracle 0 0)
    (operand : memory.registers 8 = BitVec.ofNat 256 value.val) (sizeFits : size ≤ 2 ^ 256) :
    (overlayForwardScan pairs.length memory).1.registers 8 =
      BitVec.ofNat 256 ((swaps pairs) value).val := by
  have source := overlayForward_source memory (sparseWordPairs pairs)
    (by simpa only [overlayBase_address memory oracle header] using represented.stored)
  simp only [sparseWordPairs, List.length_map, operand] at source
  exact source.trans (encoded_swaps _ (finiteWord_injective size sizeFits) pairs value)

/-- Injective word encoding also preserves the inverse sparse permutation. -/
theorem encoded_swaps_inverse {size : Nat} (pairs : List (Fin size × Fin size))
    (value : Fin size) (sizeFits : size ≤ 2 ^ 256) :
    (swaps (sparseWordPairs pairs)).symm (BitVec.ofNat 256 value.val) =
      BitVec.ofNat 256 ((swaps pairs).symm value).val := by
  apply (swaps (sparseWordPairs pairs)).injective
  rw [Equiv.apply_symm_apply]
  have encoded := encoded_swaps (fun index : Fin size => BitVec.ofNat 256 index.val)
    (finiteWord_injective size sizeFits) pairs ((swaps pairs).symm value)
  simpa only [sparseWordPairs, Equiv.apply_symm_apply] using encoded.symm

/-- The inverse overlay scan returns the encoded inverse source permutation value. -/
theorem overlayInverse_encoded {size : Nat} (memory : Memory) (oracle : Fin 15749)
    (pairs : List (Fin size × Fin size)) (represented : OverlayMemory memory.ram oracle pairs)
    (value : Fin size) (header : memory.registers 6 = oracleAddress oracle 0 0)
    (operand : memory.registers 8 = BitVec.ofNat 256 value.val) (sizeFits : size ≤ 2 ^ 256) :
    (overlayInverseScan pairs.length memory).1.registers 8 =
      BitVec.ofNat 256 ((swaps pairs).symm value).val := by
  have source := overlayInverse_source memory (sparseWordPairs pairs)
    (by simpa only [overlayHeader_address memory oracle header, sparseWordPairs, List.length_map] using represented.count)
    (by simpa only [overlayBase_address memory oracle header] using represented.stored)
  simp only [sparseWordPairs, List.length_map, operand] at source
  exact source.trans (encoded_swaps_inverse pairs value sizeFits)

end Kriterion.ArgoMAC.ArithmeticSimulator
