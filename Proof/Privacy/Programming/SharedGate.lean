import Construction.SharedGarbling
import Proof.Privacy.PaperConstruction

namespace Kriterion.ArgoMAC.Shared
open BN254 Cryptography

/-- Both branches use assignments in the same three public permutations. -/
theorem gate_programmed (oracle : PermutationOracle FixedKeyIndex Block)
    (location : Pipeline.FixedKeyLocation) (position : Fin coordinateBitCount)
    (hashLabel padLabel : Block) (hashBlocks : Fin 3 → Block) (padBlocks : Fin 2 → Block)
    (hashAssigned : ∀ slot, oracle.permutation ⟨location.kind, position, slot⟩
      (hashLabel ^^^ location.tweak) = hashBlocks slot ^^^ (hashLabel ^^^ location.tweak))
    (padAssigned : ∀ slot, oracle.permutation ⟨location.kind, position, slot.castSucc⟩
      (padLabel ^^^ location.tweak) = padBlocks slot ^^^ (padLabel ^^^ location.tweak)) :
    (Pipeline.fixedKeyGate (expandOracle oracle) location position.val).hashToField hashLabel =
      (((hashBlocks 2 ++ hashBlocks 1 ++ hashBlocks 0).toNat) : BaseField) ∧
    ∀ message, (Pipeline.fixedKeyGate (expandOracle oracle) location position.val).encrypt
      padLabel message = (padBlocks 1 ++ padBlocks 0) ^^^ BitAdaptor.fieldBytes message := by
  have hashValue (slot : Fin 3) :
      PaperConstruction.paperBlock (oracle.permutation ⟨location.kind, position, slot⟩)
        location.tweak hashLabel = hashBlocks slot := by
    rw [PaperConstruction.paperBlock, hashAssigned, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]
  have padValue (slot : Fin 2) :
      PaperConstruction.paperBlock (oracle.permutation ⟨location.kind, position, slot.castSucc⟩)
        location.tweak padLabel = padBlocks slot := by
    rw [PaperConstruction.paperBlock, padAssigned, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]
  constructor
  · rw [PaperConstruction.fixedKeyGate_hashToField_eq]
    simp only [PaperConstruction.paperHashBytes, Pipeline.fixedKeyPermutations,
      expandOracle, fixedIndex, slotIndex, Nat.mod_eq_of_lt position.isLt, hashValue]
  · intro message
    rw [PaperConstruction.fixedKeyGate_encrypt_eq]
    simp only [PaperConstruction.paperPadBytes, Pipeline.fixedKeyPermutations,
      expandOracle, fixedIndex, slotIndex, Nat.mod_eq_of_lt position.isLt, padValue]

end Kriterion.ArgoMAC.Shared
