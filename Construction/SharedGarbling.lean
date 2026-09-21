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

/-- Private coins do not contain random public oracle tables. -/
def emptyOracle : PublicOracle FixedKeyIndex EncPRF.PermutationIndex :=
  (⟨fun _ => Equiv.refl Block⟩, ⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0))

def replaceOracle (tape : Randomness)
    (oracle : PublicOracle FixedKeyIndex EncPRF.PermutationIndex) : Randomness :=
  ⟨{tape.val with
      fixedKeyOracle := expandOracle oracle.1
      encPRFOracle := oracle.2.1
      hashOracle := oracle.2.2}, by simp⟩

abbrev PrivateCoins := {tape : Randomness // replaceOracle tape emptyOracle = tape}

def privateCoins (tape : Randomness) : PrivateCoins :=
  ⟨replaceOracle tape emptyOracle, rfl⟩

def splitCoins : Randomness ≃ PrivateCoins × PublicOracle FixedKeyIndex EncPRF.PermutationIndex where
  toFun tape := (privateCoins tape, evaluationOracle tape)
  invFun pair := replaceOracle pair.1.val pair.2
  left_inv tape := by
    apply Subtype.ext
    dsimp [replaceOracle, privateCoins, evaluationOracle]
    rw [tape.property]
  right_inv pair := by
    rcases pair with ⟨⟨tape, equal⟩, ⟨fixed, enc, hash⟩⟩
    apply Prod.ext
    · apply Subtype.ext
      exact equal
    · simp [evaluationOracle, replaceOracle, restrict_expand]

/-- The executable interface keeps only the input labels in the encoding key. -/
def programCircuit [FieldCertificate] [GroupCertificate] :
    GarbledCircuit NonZeroScalar AffineInput (Option Point)
      (PrivateCoins × PublicOracle FixedKeyIndex EncPRF.PermutationIndex)
      Pipeline.Table InputMacKey GarbledCircuit.LamportSignature
      (PublicOracle FixedKeyIndex EncPRF.PermutationIndex) where
  function := wireCircuit.function
  garble parameter scalar tape :=
    ((wireCircuit.garble parameter scalar (replaceOracle tape.1.val tape.2)).1,
      tape.1.val.val.inputMacKey)
  encode key input := Lamport.selectedLabels (key.encode (BitInput.ofAffine input))
  evaluate := wireCircuit.evaluate

/-- The transmitted form of the executable interface. The garbler publishes the
packed table; the evaluator restores the removed pad bits, which it recomputes
from the public oracle anyway. -/
def packedProgramCircuit [FieldCertificate] [GroupCertificate] :
    GarbledCircuit NonZeroScalar AffineInput (Option Point)
      (PrivateCoins × PublicOracle FixedKeyIndex EncPRF.PermutationIndex)
      Pipeline.PackedTable InputMacKey GarbledCircuit.LamportSignature
      (PublicOracle FixedKeyIndex EncPRF.PermutationIndex) :=
  programCircuit.mapPublic Pipeline.Table.pack Pipeline.PackedTable.unpack

/-- The packed executable interface under the exact type the challenge's
`scheme` field declares. The field's own type is a function, so a submission
that assigns a lambda there forces the kernel to reduce that lambda inside every
later field type before it can compare the two forms; assigning this constant
instead keeps every comparison syntactic. The type is written with explicit
binders and with the challenge's own spellings of the parameters so that it is
the same term, not merely a definitionally equal one. -/
def packedProgramScheme (field : FieldCertificate) (group : @GroupCertificate field) :
    GarbledCircuit BN254.NonZeroScalar BN254.AffineInput (Option (@BN254.Point field))
      (Shared.PrivateCoins × Cryptography.PublicOracle Shared.FixedKeyIndex
        EncPRF.PermutationIndex)
      Pipeline.PackedTable InputMacKey GarbledCircuit.LamportSignature
      (Cryptography.PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) :=
  @packedProgramCircuit field group

end Kriterion.ArgoMAC.Shared
