/-
This file connects `C_1`, `C_23`, and `C_45`.
The active paper shows this pipeline at `fig:garbled_c_with_cm_opt`.
-/

import Construction.ArgoMAC.CurveMembership
import Construction.ArgoMAC.EncPRF
import Construction.ArgoMAC.FieldMacToECMac

namespace Kriterion.ArgoMAC.Pipeline

open BN254 Cryptography

def curveDigitAdaptorCount : Nat := 5
def pointDigitAdaptorsPerOutput : Nat := 12

def digitAdaptorCount : Nat :=
  curveDigitAdaptorCount + FieldMacToECMac.outputMacCount * pointDigitAdaptorsPerOutput

/-- Each fixed-key bucket holds one label pair and separates its gates by a digit tweak.
A bucket has three hash permutations and two pad permutations. -/
def bucketSlotCount : Nat := 5

def pointBucketCount : Nat :=
  pointDigitAdaptorsPerOutput * coordinateBitCount * bucketSlotCount

def curveBucketCount : Nat :=
  curveDigitAdaptorCount * coordinateBitCount * bucketSlotCount

/-- One point bucket serves one gate for each output digit. -/
def digitsPerBucket : Nat := FieldMacToECMac.outputMacCount

theorem pointBucketCountValue : pointBucketCount = 15240 := by decide
theorem curveBucketCountValue : curveBucketCount = 6350 := by decide

inductive CurveAdaptor
  | y4 | y6 | x3 | x5 | x7
deriving DecidableEq

instance : Fintype CurveAdaptor := ⟨{.y4, .y6, .x3, .x5, .x7}, fun value => by cases value <;> simp⟩

inductive PointCoordinate
  | x | y | z
deriving DecidableEq

instance : Fintype PointCoordinate := ⟨{.x, .y, .z}, fun value => by cases value <;> simp⟩

inductive PointAdaptor
  | y6 | y8 | y10 | x7 | x9
deriving DecidableEq

instance : Fintype PointAdaptor := ⟨{.y6, .y8, .y10, .x7, .x9}, fun value => by cases value <;> simp⟩

inductive FixedKeyLocation
  | curve (adaptor : CurveAdaptor)
  | point (output : Fin FieldMacToECMac.outputMacCount)
      (coordinate : PointCoordinate) (adaptor : PointAdaptor)
deriving DecidableEq, Fintype

/-- A bucket kind is one adaptor family. The output digit is not part of it. -/
inductive FixedKeyKind
  | curve (adaptor : CurveAdaptor)
  | point (coordinate : PointCoordinate) (adaptor : PointAdaptor)
deriving DecidableEq, Fintype

inductive FixedKeySlot
  | hash (slot : Fin 3)
  | pad (slot : Fin 2)
deriving DecidableEq, Fintype

/-- This index selects one public fixed-key permutation: one bucket and one slot. -/
structure FixedKeyIndex where
  kind : FixedKeyKind
  position : Fin coordinateBitCount
  slot : FixedKeySlot
deriving DecidableEq, Fintype

def FixedKeyLocation.kind : FixedKeyLocation → FixedKeyKind
  | .curve adaptor => .curve adaptor
  | .point _ coordinate adaptor => .point coordinate adaptor

/-- The paper assigns tweaks 0 through 90 to digits and tweak 91 to curve gates. -/
def FixedKeyLocation.tweak : FixedKeyLocation → Block
  | .curve _ => BitVec.ofNat 128 FieldMacToECMac.outputMacCount
  | .point output _ _ => BitVec.ofNat 128 output.val

/-- The tweak map is an involution on blocks. -/
def tweakEquiv (tweak : Block) : Equiv Block Block where
  toFun block := block ^^^ tweak
  invFun block := block ^^^ tweak
  left_inv block := by
    show block ^^^ tweak ^^^ tweak = block
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  right_inv block := by
    show block ^^^ tweak ^^^ tweak = block
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Each gate reads the raw bucket permutations. The gate applies the input tweak. -/
def fixedKeyPermutations
    (oracle : PermutationOracle FixedKeyIndex Block)
    (location : FixedKeyLocation) (position : Nat) : BitAdaptor.FixedKeyPermutations := {
  hash := fun slot => oracle.permutation {
    kind := location.kind
    position := ⟨position % coordinateBitCount, Nat.mod_lt _ (by decide)⟩
    slot := .hash slot
  }
  pad := fun slot => oracle.permutation {
    kind := location.kind
    position := ⟨position % coordinateBitCount, Nat.mod_lt _ (by decide)⟩
    slot := .pad slot
  }
}

/-- This oracle serves the gate of one location at one coordinate bit position. -/
def fixedKeyGate (oracle : PermutationOracle FixedKeyIndex Block)
    (location : FixedKeyLocation) (position : Nat) : BitAdaptor.FixedKeyOracle :=
  let gate := BitAdaptor.fixedKeyOracle (fixedKeyPermutations oracle location position)
  { hashToField label := gate.hashToField (label ^^^ location.tweak)
    encrypt label message := gate.encrypt (label ^^^ location.tweak) message
    decrypt label ciphertext := gate.decrypt (label ^^^ location.tweak) ciphertext
    decryptEncrypt label message := gate.decryptEncrypt (label ^^^ location.tweak) message }

def curveOracles (oracle : PermutationOracle FixedKeyIndex Block) :
    CurveMembership.Oracles := {
  y4 := fixedKeyGate oracle (.curve .y4)
  y6 := fixedKeyGate oracle (.curve .y6)
  x3 := fixedKeyGate oracle (.curve .x3)
  x5 := fixedKeyGate oracle (.curve .x5)
  x7 := fixedKeyGate oracle (.curve .x7)
}

def biquadraticOracles (oracle : PermutationOracle FixedKeyIndex Block)
    (output : Fin FieldMacToECMac.outputMacCount) (coordinate : PointCoordinate) :
    Biquadratic.Oracles := {
  y6 := fixedKeyGate oracle (.point output coordinate .y6)
  y8 := fixedKeyGate oracle (.point output coordinate .y8)
  y10 := fixedKeyGate oracle (.point output coordinate .y10)
  x7 := fixedKeyGate oracle (.point output coordinate .x7)
  x9 := fixedKeyGate oracle (.point output coordinate .x9)
}

def pointOracles (oracle : PermutationOracle FixedKeyIndex Block) :
    FieldMacToECMac.Oracles :=
  Vector.ofFn fun output => {
    x := biquadraticOracles oracle output .x
    y := biquadraticOracles oracle output .y
    z := biquadraticOracles oracle output .z
  }

/-- This table contains the logical `PublicCircuitState`. -/
structure Table where
  curve : CurveMembership.Table
  pointMAC : FieldMacToECMac.Table

def garble (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness)
    (bridgeKey : BaseField) (curveMask : NonZeroBase) (curveR1 curveR2 : BaseField)
    (fixedKeyOracle : PermutationOracle FixedKeyIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (inputKey : InputMacKey) : Table :=
  let pointInputKey := EncPRF.transformKey encPRFOracle
    (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey
  { curve := CurveMembership.garble bridgeKey curveMask.value curveR1 curveR2
      (curveOracles fixedKeyOracle) inputKey
    pointMAC := FieldMacToECMac.garble
      (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness)
      pointRandomness (pointOracles fixedKeyOracle) pointInputKey }

def evaluate [FieldCertificate]
    (fixedKeyOracle : PermutationOracle FixedKeyIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (table : Table)
    (input : BitInput) (inputMac : InputMac) : Option FieldMacToECMac.Result :=
  let affineInput := input.toAffine
  match decodePoint affineInput with
  | none => none
  | some _ =>
      let bridgeKey := CurveMembership.evaluate (curveOracles fixedKeyOracle)
        table.curve affineInput inputMac
      let pointInputMac := EncPRF.transformMac encPRFOracle
        (EncPRF.whiteningKeys hashOracle bridgeKey) input inputMac
      some (FieldMacToECMac.evaluate table.pointMAC (pointOracles fixedKeyOracle)
        affineInput pointInputMac)

theorem evaluateEncoded [FieldCertificate]
    (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness)
    (bridgeKey : BaseField) (curveMask : NonZeroBase) (curveR1 curveR2 : BaseField)
    (fixedKeyOracle : PermutationOracle FixedKeyIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (inputKey : InputMacKey)
    (input : AffineInput) (point : Point) (decoded : decodePoint input = some point) :
    evaluate fixedKeyOracle encPRFOracle hashOracle
        (garble outputKeys pointRandomness bridgeKey curveMask
          curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle inputKey)
        (BitInput.ofAffine input) (inputKey.encode (BitInput.ofAffine input)) =
      some (FieldMacToECMac.expectedResult
        (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness) input) := by
  have inputOnCurve : OnCurve input := (decodePoint_defined input).mp (by simp [decoded])
  simp only [evaluate, BitInput.toAffineOfAffine, decoded, garble]
  rw [InputMacKey.encodeOfAffine]
  rw [CurveMembership.evaluateEncodedOnCurve bridgeKey curveMask.value curveR1 curveR2
    (curveOracles fixedKeyOracle) inputKey input inputOnCurve]
  rw [← InputMacKey.encodeOfAffine inputKey input]
  rw [EncPRF.transformEncode]
  rw [InputMacKey.encodeOfAffine]
  rw [FieldMacToECMac.evaluateEncoded _ _ _ _ _ inputOnCurve]
  exact FieldMacToECMac.rowsForOutputKeysSparse outputKeys pointRandomness

end Kriterion.ArgoMAC.Pipeline
