import Proof.Privacy.Simulator.Arithmetic.AppendPublicFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- Agreement on the two base regions preserves the selected sparse permutation. -/
theorem SparseMemory.baseCongr (original updated : Word → Word) (oracle : Fin 15749)
    (state : SparsePermutation (2 ^ 128)) (represented : SparseMemory original oracle state)
    (fits : 2 * state.used ≤ 2 ^ 110)
    (same : ∀ region, region = (0 : Fin 4) ∨ region = 1 → ∀ offset, offset < 2 ^ 110 →
      updated (oracleAddress oracle region offset) = original (oracleAddress oracle region offset)) :
    SparseMemory updated oracle state := by
  refine ⟨⟨represented.inputLength, represented.outputLength, ?_, ?_⟩,
    (same 0 (Or.inl rfl) 0 (by decide)).trans represented.count⟩
  · apply RepresentsPairs.congr _ original updated _ represented.inputs
    intro index bound
    have len : (sparseWordPairs state.inputs).length = state.used := by
      simp only [sparseWordPairs, List.length_map, represented.inputLength]
    rw [len] at bound
    rw [oracleAddress_add]
    exact same 0 (Or.inl rfl) _ (by omega)
  · apply RepresentsPairs.congr _ original updated _ represented.outputs
    intro index bound
    have len : (sparseWordPairs state.outputs).length = state.used := by
      simp only [sparseWordPairs, List.length_map, represented.outputLength]
    rw [len] at bound
    rw [oracleAddress_add]
    exact same 1 (Or.inr rfl) _ (by omega)

/-- Agreement outside the history region preserves the finite programmed permutation. -/
theorem ProgrammedMemory.publicCongr (original updated : Word → Word) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (represented : ProgrammedMemory original oracle state)
    (fits : 2 * state.base.used ≤ 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110)
    (same : ∀ region, region ≠ (3 : Fin 4) → ∀ offset, offset < 2 ^ 110 →
      updated (oracleAddress oracle region offset) = original (oracleAddress oracle region offset)) :
    ProgrammedMemory updated oracle state := by
  constructor
  · apply SparseMemory.baseCongr original updated oracle state.base represented.base fits
    intro region choice
    rcases choice with rfl | rfl
    · exact same 0 (by decide)
    · exact same 1 (by decide)
  · exact OverlayMemory.congr original updated oracle state.overlay represented.overlay overlayFits (same 2 (by decide))

/-- Agreement outside all history regions preserves the complete oracle family. -/
theorem OracleFamilyMemory.publicCongr (original updated : Word → Word) (state : SparseOracleFamily)
    (represented : OracleFamilyMemory original state) (fits : OracleFamilyFits state)
    (same : ∀ oracle region, region ≠ (3 : Fin 4) → ∀ offset, offset < 2 ^ 110 →
      updated (oracleAddress oracle region offset) = original (oracleAddress oracle region offset)) :
    OracleFamilyMemory updated state := by
  constructor
  · intro index
    exact ProgrammedMemory.publicCongr original updated index.castSucc _ (represented.permutations index)
      (fits.base index) (fits.overlay index) (same index.castSucc)
  · apply HashMemory.congr original updated 15748 _ represented.hash
    · simpa only [hashWordPairs, List.length_map] using fits.hash
    · exact same 15748 0 (by decide)

/-- A history append preserves every finite oracle table. -/
theorem historyAppended_family (memory : Memory) (state : SparseOracleFamily)
    (oracle : Fin 15749) (count : Nat)
    (represented : OracleFamilyMemory memory.ram state) (fits : OracleFamilyFits state)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (counter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 count)
    (capacity : 257 + 2 * count < 2 ^ 110) :
    OracleFamilyMemory (historyAppended memory).ram state := by
  apply OracleFamilyMemory.publicCongr memory.ram _ state represented fits
  intro other region separate offset bound
  exact historyAppended_publicFrame memory oracle other count header counter capacity region offset bound (Or.inr separate)

/-- A recorded public reply preserves every finite oracle table. -/
theorem publicHistoryResult_family (memory : Memory) (state : SparseOracleFamily)
    (oracle : Fin 15749) (count : Nat)
    (represented : OracleFamilyMemory memory.ram state) (fits : OracleFamilyFits state)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (counter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 count)
    (capacity : 257 + 2 * count < 2 ^ 110) :
    OracleFamilyMemory (publicHistoryResult memory).1.ram state := by
  apply OracleFamilyMemory.publicCongr memory.ram _ state represented fits
  intro other region separate offset bound
  exact publicHistoryResult_publicFrame memory oracle other count header counter capacity region offset bound (Or.inr separate)

end Kriterion.ArgoMAC.ArithmeticSimulator
