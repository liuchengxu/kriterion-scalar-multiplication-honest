/-
This file defines the ArgoMAC garbling scheme.
-/

import Construction.ArgoMAC
import Construction.ArgoMAC.Packed
import GarbledCircuit

namespace Kriterion.GarbledCircuit

/-- This adapter shrinks the transmitted public value. Evaluation restores the
removed part, so a scheme that never reads it keeps every property. -/
def mapPublic (scheme : GarbledCircuit Circuit Input Output Randomness Public Key Labels Oracle)
    (pack : Public → Packed) (unpack : Packed → Public) :
    GarbledCircuit Circuit Input Output Randomness Packed Key Labels Oracle where
  function := scheme.function
  garble parameter circuit randomness :=
    let result := scheme.garble parameter circuit randomness
    (pack result.1, result.2)
  encode := scheme.encode
  evaluate oracle transmitted input labels := scheme.evaluate oracle (unpack transmitted) input labels

end Kriterion.GarbledCircuit

namespace Kriterion.ArgoMAC.Garbling

open BN254 Cryptography

/-- This structure contains every explicit garbling input. -/
structure Randomness where
  offsets : FieldMacToECMac.SuccessfulOffsets
  offsetsClamped : ∀ [FieldCertificate] [GroupCertificate], offsets.IsClamped
  pointRandomness : FieldMacToECMac.Randomness
  bridgeKey : BaseField
  curveMask : NonZeroBase
  curveR1 : BaseField
  curveR2 : BaseField
  fixedKeyOracle : PermutationOracle Pipeline.FixedKeyIndex Block
  inputMacKey : InputMacKey
  encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block
  hashOracle : EncPRF.HashOracle

structure EncodingKey where
  scalar : NonZeroScalar
  randomness : Randomness

structure Labels where
  input : BitInput
  inputMac : InputMac

abbrev PublicCircuit := Pipeline.Table

abbrev EvaluationOracle := PublicOracle Pipeline.FixedKeyIndex EncPRF.PermutationIndex
abbrev OracleQuery := PublicQuery Pipeline.FixedKeyIndex EncPRF.PermutationIndex
abbrev OracleAnswer := @PublicQuery.Answer Pipeline.FixedKeyIndex EncPRF.PermutationIndex
abbrev oracleSpec := publicOracleSpec Pipeline.FixedKeyIndex EncPRF.PermutationIndex

/-- The handler exposes every oracle that evaluation reads. -/
def oracleHandler : OracleHandler oracleSpec Randomness :=
  publicHandler fun randomness =>
    (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)

structure Topology where
  coordinateBits : Nat
  outputDigits : Nat

def garble (construction : Construction) (scalar : NonZeroScalar)
    (randomness : Randomness) : PublicCircuit × EncodingKey :=
  (Pipeline.garble
      (FieldMacToECMac.outputKeys construction scalar.value randomness.offsets)
      randomness.pointRandomness randomness.bridgeKey
      randomness.curveMask randomness.curveR1 randomness.curveR2
      randomness.fixedKeyOracle randomness.encPRFOracle randomness.hashOracle
      randomness.inputMacKey,
    { scalar, randomness })

def encode (key : EncodingKey) (input : BitInput) : Labels := {
  input
  inputMac := key.randomness.inputMacKey.encode input
}

def decodeHomogeneous [FieldCertificate]
    (value : FieldMacToECMac.HomogeneousValue) : Option Point :=
  if value.z = 0 then
    if value.x = 0 ∧ value.y ≠ 0 then some 0 else none
  else
    decodePoint { x := value.x / value.z, y := value.y / value.z }

def decodePointMacs [FieldCertificate]
    (values : Vector FieldMacToECMac.HomogeneousValue FieldMacToECMac.outputMacCount) :
    Option (List Point) :=
  values.toList.mapM decodeHomogeneous

def decodeResult [FieldCertificate] [GroupCertificate]
    (result : FieldMacToECMac.Result) : Option Point :=
  (decodePointMacs result.pointMacs).map (pointHorner radix)

def evaluate [FieldCertificate] [GroupCertificate] (oracle : EvaluationOracle)
    (table : PublicCircuit) (labels : Labels) : Option Point :=
  (Pipeline.evaluate oracle.1 oracle.2.1 oracle.2.2
    table labels.input labels.inputMac).bind decodeResult

/-- Correct labels evaluate all table rows. -/
theorem evaluateEncodeRows [FieldCertificate] (construction : Construction)
    (key : EncodingKey) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) :
    Pipeline.evaluate key.randomness.fixedKeyOracle key.randomness.encPRFOracle
        key.randomness.hashOracle (garble construction key.scalar key.randomness).1
        (BitInput.ofAffine input) (encode key (BitInput.ofAffine input)).inputMac =
      some (FieldMacToECMac.expectedResult
        (FieldMacToECMac.rowsForOutputKeys
          (FieldMacToECMac.outputKeys construction key.scalar.value key.randomness.offsets)
          key.randomness.pointRandomness) input) := by
  exact Pipeline.evaluateEncoded
    (FieldMacToECMac.outputKeys construction key.scalar.value key.randomness.offsets)
    key.randomness.pointRandomness
    key.randomness.bridgeKey key.randomness.curveMask
    key.randomness.curveR1 key.randomness.curveR2 key.randomness.fixedKeyOracle
    key.randomness.encPRFOracle key.randomness.hashOracle
    key.randomness.inputMacKey input point decoded

def garbledCircuit [FieldCertificate] [GroupCertificate] (construction : Construction) :
    GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness PublicCircuit
      EncodingKey Labels EvaluationOracle := {
  function := fun scalar input => checkedScalarMultiplication scalar.value input
  garble := fun _ scalar randomness => garble construction scalar randomness
  encode := fun key input => encode key (BitInput.ofAffine input)
  evaluate := fun oracle table _ labels => some (evaluate oracle table labels)
}

def topology (_scalar : NonZeroScalar) : Topology := {
  coordinateBits := 508
  outputDigits := 91
}

end Kriterion.ArgoMAC.Garbling

namespace Kriterion.ArgoMAC.Lamport
open BN254 Cryptography

def keyPairs (key : InputMacKey) : GarbledCircuit.LamportSecretKey :=
  Vector.ofFn fun index =>
    if low : index.val < 254 then
      let item := key.x.get ⟨index.val, low⟩
      (item.falseLabel, item.trueLabel)
    else
      let item := key.y.get ⟨index.val - 254, by
        change index.val - 254 < 254
        omega⟩
      (item.falseLabel, item.trueLabel)

def selectedLabels (mac : InputMac) : GarbledCircuit.LamportSignature :=
  Vector.ofFn fun index =>
    if low : index.val < 254 then
      mac.x.get ⟨index.val, low⟩
    else
      mac.y.get ⟨index.val - 254, by
        change index.val - 254 < 254
        omega⟩

/-- The evaluator reconstructs its internal labels from its input and 508 blocks. -/
def restore (input : AffineInput) (labels : GarbledCircuit.LamportSignature) : Garbling.Labels := {
  input := BitInput.ofAffine input
  inputMac := {
    x := Vector.ofFn fun index => labels[index.val]'(by have : index.val < 254 := index.isLt; omega)
    y := Vector.ofFn fun index => labels[254 + index.val]'(by have : index.val < 254 := index.isLt; omega)
  }
}

/-- This adapter removes the repeated input from the transmitted labels. -/
def wireCircuit [FieldCertificate] [GroupCertificate] :=
  (Garbling.garbledCircuit construction).mapLabels (fun labels => selectedLabels labels.inputMac) restore

/-- This adapter removes the two pad bits that no ciphertext uses for a message.
The evaluator recomputes the pad, so it restores them itself. -/
def packedCircuit [FieldCertificate] [GroupCertificate] :=
  wireCircuit.mapPublic Pipeline.Table.pack Pipeline.PackedTable.unpack

end Kriterion.ArgoMAC.Lamport
