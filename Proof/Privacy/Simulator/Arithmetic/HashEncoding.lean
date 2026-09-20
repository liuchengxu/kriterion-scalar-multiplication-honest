import Proof.Privacy.Simulator.Arithmetic.HashQueryMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The hash table stores each finite answer in one full machine word. -/
def hashWordPairs {Key : Type} (encode : Key → Word) (pairs : HashTable Key (2 ^ 256)) :
    List (Word × Word) :=
  pairs.map fun pair => (encode pair.1, BitVec.ofNat 256 pair.2.val)

/-- An injective key encoding preserves the first-match lookup rule. -/
theorem hashWordPairs_lookup {Key : Type} [DecidableEq Key] (encode : Key → Word)
    (injective : Function.Injective encode) (pairs : HashTable Key (2 ^ 256)) (key : Key) :
    (hashWordPairs encode pairs).lookup (encode key) =
      (pairs.lookup key).map (fun value => BitVec.ofNat 256 value.val) := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨input, value⟩
      by_cases same : key = input
      · subst input
        simp [hashWordPairs, List.lookup]
      · have encoded : encode key ≠ encode input := fun equal => same (injective equal)
        have keyDifferent : (key == input) = false := beq_eq_false_iff_ne.mpr same
        have wordDifferent : (encode key == encode input) = false := beq_eq_false_iff_ne.mpr encoded
        simpa [hashWordPairs, List.lookup, keyDifferent, wordDifferent] using ih

/-- Full-width conversion retains every finite hash answer. -/
theorem hashWord_toFin (value : Fin (2 ^ 256)) :
    (BitVec.ofNat 256 value.val).toFin = value := by
  apply Fin.ext
  simp [Nat.mod_eq_of_lt value.isLt]

/-- Full-width words and finite hash answers have the same uniform law. -/
theorem hashWord_uniform :
    (PMF.uniformOfFintype Word).map BitVec.toFin = PMF.uniformOfFintype (Fin (2 ^ 256)) := by
  exact PMF.uniformOfFintype_map_of_bijective _ (BitVec.equivFin (m := 256)).bijective

/-- Canonical BN254 field values have distinct machine-word encodings. -/
theorem hashKeyWord_injective : Function.Injective (fun value : BN254.BaseField => BitVec.ofNat 256 value.val) := by
  intro left right equal
  have leftBound : left.val < 2 ^ 256 := lt_trans left.val_lt (by decide : BN254.baseFieldModulus < 2 ^ 256)
  have rightBound : right.val < 2 ^ 256 := lt_trans right.val_lt (by decide : BN254.baseFieldModulus < 2 ^ 256)
  have values := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt rightBound] at values
  exact ZMod.val_injective _ values

end Kriterion.ArgoMAC.ArithmeticSimulator
