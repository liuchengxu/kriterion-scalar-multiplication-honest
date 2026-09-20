import Proof.Privacy.Simulator.Arithmetic.OracleMemoryCongr
import Proof.Privacy.Simulator.Arithmetic.ProgrammedForwardJoint
import Proof.Privacy.Simulator.Arithmetic.ProgrammedInverseSource
import Proof.Privacy.Simulator.Arithmetic.HashSourceMemory
import Proof.Privacy.Simulator.Arithmetic.PermutationOtherOracle
import Proof.Privacy.Simulator.Arithmetic.HashOtherOracle

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The finite source stores every physical permutation and the hash table. -/
structure SparseOracleFamily where
  permutations : Fin 15748 → ProgrammedPermutation (2 ^ 128)
  hash : HashTable BN254.BaseField (2 ^ 256)

/-- The physical hash keys use their canonical field representatives. -/
def hashKeyWord (value : BN254.BaseField) : Word := BitVec.ofNat 256 value.val

/-- The family relation connects every finite source table to its physical RAM region. -/
structure OracleFamilyMemory (ram : Word → Word) (state : SparseOracleFamily) : Prop where
  permutations : ∀ index, ProgrammedMemory ram index.castSucc (state.permutations index)
  hash : HashMemory ram 15748 (hashWordPairs hashKeyWord state.hash)

/-- The source tables fit their disjoint physical regions. -/
structure OracleFamilyFits (state : SparseOracleFamily) : Prop where
  base : ∀ index, 2 * (state.permutations index).base.used ≤ 2 ^ 110
  overlay : ∀ index, 256 + 2 * (state.permutations index).overlay.length < 2 ^ 110
  hash : 2 * state.hash.length ≤ 2 ^ 110

/-- A source permutation update preserves the other finite tables. -/
def SparseOracleFamily.updatePermutation (state : SparseOracleFamily) (index : Fin 15748)
    (next : ProgrammedPermutation (2 ^ 128)) : SparseOracleFamily :=
  { state with permutations := Function.update state.permutations index next }

/-- A source hash update preserves every finite permutation. -/
def SparseOracleFamily.updateHash (state : SparseOracleFamily)
    (next : HashTable BN254.BaseField (2 ^ 256)) : SparseOracleFamily := {state with hash := next}

/-- Agreement on one oracle preserves its complete programmed memory relation. -/
theorem ProgrammedMemory.congr (original updated : Word → Word) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (represented : ProgrammedMemory original oracle state)
    (fits : 2 * state.base.used ≤ 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110)
    (same : ∀ table offset, offset < 2 ^ 110 →
      updated (oracleAddress oracle table offset) = original (oracleAddress oracle table offset)) :
    ProgrammedMemory updated oracle state :=
  ⟨SparseMemory.congr original updated oracle state.base represented.base fits same,
    OverlayMemory.congr original updated oracle state.overlay represented.overlay overlayFits (same 2)⟩

/-- Agreement on every public oracle cell preserves the complete family relation. -/
theorem OracleFamilyMemory.congr (original updated : Word → Word) (state : SparseOracleFamily)
    (represented : OracleFamilyMemory original state) (fits : OracleFamilyFits state)
    (same : ∀ oracle table offset, offset < 2 ^ 110 →
      updated (oracleAddress oracle table offset) = original (oracleAddress oracle table offset)) :
    OracleFamilyMemory updated state := by
  constructor
  · intro index
    exact ProgrammedMemory.congr original updated index.castSucc _ (represented.permutations index)
      (fits.base index) (fits.overlay index) (same index.castSucc)
  · apply HashMemory.congr original updated 15748 _ represented.hash
    · simpa only [hashWordPairs, List.length_map] using fits.hash
    · exact same 15748 0

/-- Every permutation region differs from the final hash region. -/
theorem permutationIndex_ne_hash (index : Fin 15748) : index.castSucc ≠ (15748 : Fin 15749) := by
  intro equal
  have same := congrArg Fin.val equal
  exact Nat.ne_of_lt index.isLt same

/-- A selected permutation update lifts to the complete physical oracle family. -/
theorem OracleFamilyMemory.updatePermutation (original updated : Word → Word) (state : SparseOracleFamily)
    (index : Fin 15748) (next : ProgrammedPermutation (2 ^ 128))
    (represented : OracleFamilyMemory original state) (fits : OracleFamilyFits state)
    (selected : ProgrammedMemory updated index.castSucc next)
    (others : ∀ other : Fin 15749, other ≠ index.castSucc → ∀ table offset, offset < 2 ^ 110 →
      updated (oracleAddress other table offset) = original (oracleAddress other table offset)) :
    OracleFamilyMemory updated (state.updatePermutation index next) := by
  constructor
  · intro other
    by_cases same : other = index
    · subst other
      simpa only [SparseOracleFamily.updatePermutation, Function.update_self] using selected
    · simp only [SparseOracleFamily.updatePermutation, Function.update_of_ne same]
      apply ProgrammedMemory.congr original updated other.castSucc _ (represented.permutations other)
        (fits.base other) (fits.overlay other)
      exact others other.castSucc (fun equal => same (Fin.castSucc_injective _ equal))
  · apply HashMemory.congr original updated 15748 _ represented.hash
    · simpa only [hashWordPairs, List.length_map] using fits.hash
    · exact others 15748 (Ne.symm (permutationIndex_ne_hash index)) 0

/-- A hash update lifts to the complete physical oracle family. -/
theorem OracleFamilyMemory.updateHash (original updated : Word → Word) (state : SparseOracleFamily)
    (next : HashTable BN254.BaseField (2 ^ 256))
    (represented : OracleFamilyMemory original state) (fits : OracleFamilyFits state)
    (selected : HashMemory updated 15748 (hashWordPairs hashKeyWord next))
    (others : ∀ other : Fin 15749, other ≠ 15748 → ∀ table offset, offset < 2 ^ 110 →
      updated (oracleAddress other table offset) = original (oracleAddress other table offset)) :
    OracleFamilyMemory updated (state.updateHash next) := by
  constructor
  · intro index
    exact ProgrammedMemory.congr original updated index.castSucc _ (represented.permutations index)
      (fits.base index) (fits.overlay index) (others index.castSucc (permutationIndex_ne_hash index))
  · exact selected

end Kriterion.ArgoMAC.ArithmeticSimulator
