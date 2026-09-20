import Construction.Garbling
import Construction.ArgoMAC.Seed

namespace Kriterion.ArgoMAC.Shared
open BN254 Cryptography

/-- Each public bucket contains exactly three permutations. -/
structure FixedKeyIndex where
  kind : Pipeline.FixedKeyKind
  position : Fin coordinateBitCount
  slot : Fin 3
  deriving DecidableEq, Fintype

/-- Hash and pad roles share slots zero and one. -/
def slotIndex : Pipeline.FixedKeySlot → Fin 3
  | .hash slot => slot
  | .pad slot => slot.castSucc

def fixedIndex (index : Pipeline.FixedKeyIndex) : FixedKeyIndex :=
  ⟨index.kind, index.position, slotIndex index.slot⟩

/-- The table algorithm retains its role names and reads the shared permutations. -/
def expandOracle (oracle : PermutationOracle FixedKeyIndex Block) :
    PermutationOracle Pipeline.FixedKeyIndex Block :=
  ⟨fun index => oracle.permutation (fixedIndex index)⟩

/-- The public interface exposes one representative for each shared slot. -/
def restrictOracle (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) :
    PermutationOracle FixedKeyIndex Block :=
  ⟨fun index => oracle.permutation ⟨index.kind, index.position, .hash index.slot⟩⟩

@[simp] theorem restrict_expand (oracle : PermutationOracle FixedKeyIndex Block) :
    restrictOracle (expandOracle oracle) = oracle := by
  cases oracle
  rfl

/-- A tape stores equal permutations for the two names of a shared slot.
This constraint removes the independent pad permutations from the tape space. -/
abbrev Randomness := {tape : Garbling.Randomness //
  expandOracle (restrictOracle tape.fixedKeyOracle) = tape.fixedKeyOracle}

/-- This conversion supplies a concrete witness for the finite tape type. -/
def Randomness.ofLegacy (tape : Garbling.Randomness) : Randomness :=
  ⟨{tape with fixedKeyOracle := expandOracle (restrictOracle tape.fixedKeyOracle)}, by simp⟩

def evaluationOracle (tape : Randomness) : PublicOracle FixedKeyIndex EncPRF.PermutationIndex :=
  (restrictOracle tape.val.fixedKeyOracle, tape.val.encPRFOracle, tape.val.hashOracle)

/-- Evaluation uses the same three-slot oracle that garbling uses. -/
def wireCircuit [FieldCertificate] [GroupCertificate] :
    GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Pipeline.Table
      Garbling.EncodingKey GarbledCircuit.LamportSignature
      (PublicOracle FixedKeyIndex EncPRF.PermutationIndex) := {
  function := Lamport.wireCircuit.function
  garble := fun parameter scalar tape => Lamport.wireCircuit.garble parameter scalar tape.val
  encode := Lamport.wireCircuit.encode
  evaluate := fun oracle => Lamport.wireCircuit.evaluate (expandOracle oracle.1, oracle.2)
}

/-- This adapter removes the two pad bits that no ciphertext uses for a message.
The evaluator recomputes the pad, so it restores them itself. -/
def packedCircuit [FieldCertificate] [GroupCertificate] :
    GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Pipeline.PackedTable
      Garbling.EncodingKey GarbledCircuit.LamportSignature
      (PublicOracle FixedKeyIndex EncPRF.PermutationIndex) :=
  wireCircuit.mapPublic Pipeline.Table.pack Pipeline.PackedTable.unpack

/-- The hash role and the pad role read the identical permutation in either shared slot. -/
theorem shared_slots (oracle : PermutationOracle FixedKeyIndex Block)
    (kind : Pipeline.FixedKeyKind) (position : Fin coordinateBitCount) (slot : Fin 2) :
    (expandOracle oracle).permutation ⟨kind, position, .hash slot.castSucc⟩ =
      (expandOracle oracle).permutation ⟨kind, position, .pad slot⟩ := rfl

/-- The public slot type has the paper's cardinality. -/
theorem slot_count : Fintype.card (Fin 3) = 3 := rfl

end Kriterion.ArgoMAC.Shared
