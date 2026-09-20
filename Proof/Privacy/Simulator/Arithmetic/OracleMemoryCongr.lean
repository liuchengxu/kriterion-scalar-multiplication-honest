import Proof.Privacy.Simulator.Arithmetic.OverlayMemory
import Proof.Privacy.Simulator.Arithmetic.HashMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- Agreement on one public oracle preserves its complete sparse base relation. -/
theorem SparseMemory.congr {size : Nat} (original updated : Word → Word) (oracle : Fin 15749)
    (state : SparsePermutation size) (represented : SparseMemory original oracle state)
    (fits : 2 * state.used ≤ 2 ^ 110)
    (same : ∀ table offset, offset < 2 ^ 110 →
      updated (oracleAddress oracle table offset) = original (oracleAddress oracle table offset)) :
    SparseMemory updated oracle state := by
  exact ⟨SparseTableData.congr original updated oracle state represented.toSparseTableData fits same,
    (same 0 0 (by decide)).trans represented.count⟩

/-- Agreement on the overlay region preserves its count and its ordered swaps. -/
theorem OverlayMemory.congr {size : Nat} (original updated : Word → Word) (oracle : Fin 15749)
    (pairs : List (Fin size × Fin size)) (represented : OverlayMemory original oracle pairs)
    (fits : 256 + 2 * pairs.length < 2 ^ 110)
    (same : ∀ offset, offset < 2 ^ 110 →
      updated (oracleAddress oracle 2 offset) = original (oracleAddress oracle 2 offset)) :
    OverlayMemory updated oracle pairs := by
  refine ⟨(same 0 (by decide)).trans represented.count, ?_⟩
  apply RepresentsPairs.congr _ original updated _ represented.stored
  intro index inside
  rw [oracleAddress_add]
  exact same _ (by simp only [sparseWordPairs, List.length_map] at inside; omega)

/-- Agreement on the hash region preserves its count and its first-match pairs. -/
theorem HashMemory.congr (original updated : Word → Word) (oracle : Fin 15749)
    (pairs : List (Word × Word)) (represented : HashMemory original oracle pairs)
    (fits : 2 * pairs.length ≤ 2 ^ 110)
    (same : ∀ offset, offset < 2 ^ 110 →
      updated (oracleAddress oracle 0 offset) = original (oracleAddress oracle 0 offset)) :
    HashMemory updated oracle pairs := by
  refine ⟨(same 0 (by decide)).trans represented.count, ?_⟩
  apply RepresentsPairs.congr _ original updated _ represented.stored
  intro index inside
  rw [oracleAddress_add]
  exact same _ (by omega)

end Kriterion.ArgoMAC.ArithmeticSimulator
