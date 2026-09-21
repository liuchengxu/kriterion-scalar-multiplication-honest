import Construction.SharedGarbling
import Proof.Correctness
import Proof.CiphertextSize
import Proof.LamportCompatibility
import Proof.PackedAdapter

namespace Kriterion.ArgoMAC.Shared
open BN254

attribute [local irreducible] Wire.encoding Garbling.garble Garbling.evaluate

/-- The construction uses the packed digit count and the shared slot count. -/
theorem paperParameters : FieldMacToECMac.outputMacCount = 91 ∧
    Fintype.card (Fin 3) = 3 := ⟨rfl, rfl⟩

/-- Sharing permutations does not change the table encoding. The transmitted
value is the packed table, exactly as `Wire.encoding` writes it. -/
theorem ciphertextSize [FieldCertificate] [GroupCertificate]
    (parameter : Nat) (scalar : NonZeroScalar) (tape : Randomness) :
    (Wire.encoding.encode
      (Pipeline.Table.pack (wireCircuit.garble parameter scalar tape).1)).length = 8887896 := by
  have shared : (wireCircuit.garble parameter scalar tape).1 =
      ((Garbling.garbledCircuit construction).garble parameter scalar tape.val).1 := rfl
  rw [shared]
  exact Wire.ciphertextSize parameter scalar tape.val

/-- The packed shared circuit keeps the same byte count: it transmits the packed
table, which is what `ciphertextSize` already measures. Stating the length at
the packed garble keeps the obligation syntactically equal to the challenge's
field, so neither the elaborator nor the kernel has to unfold the encoding. -/
theorem packedCiphertextSize [FieldCertificate] [GroupCertificate]
    (parameter : Nat) (scalar : NonZeroScalar) (tape : Randomness) :
    (Wire.encoding.encode (packedCircuit.garble parameter scalar tape).1).length = 8887896 := by
  rw [show (packedCircuit.garble parameter scalar tape).1 =
    Pipeline.Table.pack (wireCircuit.garble parameter scalar tape).1 from rfl]
  exact ciphertextSize parameter scalar tape

/-- The shared-slot circuit sends the same 508 selected Lamport labels. -/
def lamportCompatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility wireCircuit affineLamportBits := {
  keyPairs := Lamport.compatible.keyPairs
  encodeSelectsLabels := Lamport.compatible.encodeSelectsLabels
}

/-- The packed shared circuit keeps the Lamport encoding obligation. -/
def packedCompatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility packedCircuit affineLamportBits :=
  lamportCompatible.mapPublic Pipeline.Table.pack Pipeline.PackedTable.unpack

/-- Correctness holds for every coherent tape and every input. -/
theorem perfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness wireCircuit evaluationOracle := by
  intro parameter scalar tape input
  dsimp only [wireCircuit, evaluationOracle, Lamport.wireCircuit,
    GarbledCircuit.mapLabels, Garbling.garbledCircuit]
  rw [tape.property]
  dsimp only [Garbling.encode]
  rw [Lamport.restore_selected]
  exact RCBComplete.perfectCorrectness parameter scalar tape.val input

/-- The stored garble of the packed circuit restores exactly what the map
removed, because evaluation reads only the transmitted bits. -/
theorem packedCircuit_evaluate [FieldCertificate] [GroupCertificate]
    (answers : Cryptography.PublicOracle FixedKeyIndex EncPRF.PermutationIndex) (parameter : Nat) (scalar : NonZeroScalar)
    (tape : Randomness) (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    wireCircuit.evaluate answers
        (Pipeline.PackedTable.unpack
          (Pipeline.Table.pack (wireCircuit.garble parameter scalar tape).1))
        input labels =
      wireCircuit.evaluate answers (wireCircuit.garble parameter scalar tape).1 input labels := by
  simpa only [wireCircuit, GarbledCircuit.mapLabels, Garbling.garbledCircuit, Garbling.garble,
    Garbling.evaluate] using
    Lamport.packedCircuit_evaluate (Shared.expandOracle answers.1, answers.2)
      parameter scalar tape.val input labels

/-- Correctness holds at the transmitted public value too. -/
theorem packedPerfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness packedCircuit evaluationOracle :=
  perfectCorrectness.mapPublic Pipeline.Table.pack Pipeline.PackedTable.unpack
    (fun answers parameter scalar tape input labels =>
      packedCircuit_evaluate answers parameter scalar tape input labels)

/-- The unpacked executable interface keeps the Lamport encoding obligation. -/
def programLamportCompatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility programCircuit affineLamportBits where
  keyPairs := Lamport.keyPairs
  encodeSelectsLabels := Lamport.selectedLabels_eq

/-- The unpacked executable interface keeps perfect correctness. -/
theorem programPerfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness programCircuit Prod.snd := by
  intro parameter scalar tape input
  have correct := perfectCorrectness parameter scalar (replaceOracle tape.1.val tape.2) input
  simpa [programCircuit, wireCircuit, Lamport.wireCircuit, GarbledCircuit.mapLabels,
    Garbling.garbledCircuit, Garbling.garble, Garbling.encode, replaceOracle,
    evaluationOracle, restrict_expand] using correct

/-- The packed executable interface keeps the byte count: its garble transmits
the packed table, which is what `ciphertextSize` already measures. -/
theorem packedProgramCiphertextSize [FieldCertificate] [GroupCertificate]
    (parameter : Nat) (scalar : NonZeroScalar)
    (tape : PrivateCoins × Cryptography.PublicOracle FixedKeyIndex EncPRF.PermutationIndex) :
    (Wire.encoding.encode (packedProgramCircuit.garble parameter scalar tape).1).length = 8887896 := by
  rw [show (packedProgramCircuit.garble parameter scalar tape).1 =
      Pipeline.Table.pack (programCircuit.garble parameter scalar tape).1 from rfl,
    show (programCircuit.garble parameter scalar tape).1 =
      (wireCircuit.garble parameter scalar (replaceOracle tape.1.val tape.2)).1 from rfl]
  exact ciphertextSize parameter scalar (replaceOracle tape.1.val tape.2)

/-- The same byte count at `packedProgramScheme`, which is the term the
challenge's `scheme` field holds in the entry. Stating it over that constant
rather than over a lambda keeps the challenge's `ciphertextSize` field
syntactically its own statement, so the kernel never unfolds the encoder while
it checks the bundle. -/
theorem packedProgramSchemeCiphertextSize (field : FieldCertificate)
    (group : @GroupCertificate field) (parameter : Nat) (scalar : NonZeroScalar)
    (tape : PrivateCoins × Cryptography.PublicOracle FixedKeyIndex EncPRF.PermutationIndex) :
    (Wire.encoding.encode ((packedProgramScheme field group).garble parameter scalar tape).1).length =
      8887896 := by
  rw [show (packedProgramScheme field group).garble parameter scalar tape =
      (@packedProgramCircuit field group).garble parameter scalar tape from rfl]
  exact @packedProgramCiphertextSize field group parameter scalar tape

/-- The packed executable interface keeps the Lamport encoding obligation. -/
def packedProgramLamportCompatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility packedProgramCircuit affineLamportBits :=
  programLamportCompatible.mapPublic Pipeline.Table.pack Pipeline.PackedTable.unpack

/-- The packed executable interface keeps perfect correctness. -/
theorem packedProgramPerfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness packedProgramCircuit Prod.snd :=
  programPerfectCorrectness.mapPublic Pipeline.Table.pack Pipeline.PackedTable.unpack
    (fun answers parameter scalar tape input labels =>
      packedCircuit_evaluate answers parameter scalar (replaceOracle tape.1.val tape.2) input labels)
