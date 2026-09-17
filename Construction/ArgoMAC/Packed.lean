/-
This file defines the transmitted table. It has the shape of `Pipeline.Table`
with the two untransmitted pad bits removed from every ciphertext row.
-/

import Construction.ArgoMAC.Pipeline

namespace Kriterion.ArgoMAC

open BN254 Cryptography

namespace BitAdaptor

/-- One transmitted bit-adaptor row. -/
structure PackedTable where
  trueRow : Payload
deriving DecidableEq

/-- This map drops the two pad bits that carry no message. -/
def Table.pack (table : Table) : PackedTable := ⟨payload table.trueRow⟩

/-- This map restores the removed bits as zeros. -/
def PackedTable.unpack (table : PackedTable) : Table := ⟨table.trueRow.setWidth 256⟩

/-- Evaluation reads only the transmitted bits. -/
@[simp] theorem payload_unpack (table : PackedTable) :
    payload table.unpack.trueRow = table.trueRow := by
  simp only [payload, PackedTable.unpack]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : coordinateBitCount ≤ 256),
    BitVec.setWidth_eq]

/-- A round trip keeps every transmitted bit. -/
@[simp] theorem payload_unpack_pack (table : Table) :
    payload table.pack.unpack.trueRow = payload table.trueRow := by
  rw [payload_unpack]
  rfl

@[simp] theorem evaluate_unpack_pack (oracle : FixedKeyOracle) (table : Table)
    (value : Bool) (input : Cryptography.Block) :
    evaluate oracle table.pack.unpack value input = evaluate oracle table value input := by
  cases value <;> simp [evaluate, Table.pack]

end BitAdaptor

namespace DigitAdaptor

/-- This is the transmitted form of one digit adaptor. -/
def pack {count : Nat} (tables : Vector BitAdaptor.Table count) :
    Vector BitAdaptor.PackedTable count :=
  tables.map BitAdaptor.Table.pack

/-- This is the restored form of one digit adaptor. -/
def unpack {count : Nat} (tables : Vector BitAdaptor.PackedTable count) :
    Vector BitAdaptor.Table count :=
  tables.map BitAdaptor.PackedTable.unpack

@[simp] theorem evaluate_unpack_pack {count : Nat}
    (windows : Nat → BitAdaptor.FixedKeyOracle) (values : Fin count → Bool)
    (tables : Vector BitAdaptor.Table count) (inputs : Vector Cryptography.Block count) :
    evaluate windows values (unpack (pack tables)) inputs =
      evaluate windows values tables inputs := by
  apply Vector.ext
  intro index inRange
  simp [evaluate, unpack, pack, Vector.get, Fin.cast]

end DigitAdaptor

namespace CurveMembership

/-- This is the transmitted curve-membership table. -/
structure PackedTable where
  c0 : BaseField
  c1 : BaseField
  c2 : BaseField
  x3 : Vector BitAdaptor.PackedTable coordinateBitCount
  x5 : Vector BitAdaptor.PackedTable coordinateBitCount
  x7 : Vector BitAdaptor.PackedTable coordinateBitCount
  y4 : Vector BitAdaptor.PackedTable coordinateBitCount
  y6 : Vector BitAdaptor.PackedTable coordinateBitCount

def Table.pack (table : Table) : PackedTable := {
  c0 := table.c0
  c1 := table.c1
  c2 := table.c2
  x3 := DigitAdaptor.pack table.x3
  x5 := DigitAdaptor.pack table.x5
  x7 := DigitAdaptor.pack table.x7
  y4 := DigitAdaptor.pack table.y4
  y6 := DigitAdaptor.pack table.y6 }

def PackedTable.unpack (table : PackedTable) : Table := {
  c0 := table.c0
  c1 := table.c1
  c2 := table.c2
  x3 := DigitAdaptor.unpack table.x3
  x5 := DigitAdaptor.unpack table.x5
  x7 := DigitAdaptor.unpack table.x7
  y4 := DigitAdaptor.unpack table.y4
  y6 := DigitAdaptor.unpack table.y6 }

@[simp] theorem evaluateDigit_unpack_pack (windows : Nat → BitAdaptor.FixedKeyOracle)
    (table : Vector BitAdaptor.Table coordinateBitCount) (value : BaseField)
    (inputMac : CoordinateMac) :
    evaluateDigit windows (DigitAdaptor.unpack (DigitAdaptor.pack table)) value inputMac =
      evaluateDigit windows table value inputMac := by
  simp [evaluateDigit]

@[simp] theorem evaluate_unpack_pack (oracles : Oracles) (table : Table)
    (input : AffineInput) (inputMac : InputMac) :
    evaluate oracles table.pack.unpack input inputMac = evaluate oracles table input inputMac := by
  simp [evaluate, Table.pack, PackedTable.unpack]

end CurveMembership

namespace Biquadratic

/-- This is the transmitted biquadratic table. -/
structure PackedTable where
  c0 : Option BaseField
  c1 : Option BaseField
  c2 : Option BaseField
  c3 : Option BaseField
  c4 : Option BaseField
  c5 : Option BaseField
  x7 : Option (Vector BitAdaptor.PackedTable coordinateBitCount)
  x9 : Option (Vector BitAdaptor.PackedTable coordinateBitCount)
  y6 : Option (Vector BitAdaptor.PackedTable coordinateBitCount)
  y8 : Option (Vector BitAdaptor.PackedTable coordinateBitCount)
  y10 : Option (Vector BitAdaptor.PackedTable coordinateBitCount)

def Table.pack (table : Table) : PackedTable := {
  c0 := table.c0
  c1 := table.c1
  c2 := table.c2
  c3 := table.c3
  c4 := table.c4
  c5 := table.c5
  x7 := table.x7.map DigitAdaptor.pack
  x9 := table.x9.map DigitAdaptor.pack
  y6 := table.y6.map DigitAdaptor.pack
  y8 := table.y8.map DigitAdaptor.pack
  y10 := table.y10.map DigitAdaptor.pack }

def PackedTable.unpack (table : PackedTable) : Table := {
  c0 := table.c0
  c1 := table.c1
  c2 := table.c2
  c3 := table.c3
  c4 := table.c4
  c5 := table.c5
  x7 := table.x7.map DigitAdaptor.unpack
  x9 := table.x9.map DigitAdaptor.unpack
  y6 := table.y6.map DigitAdaptor.unpack
  y8 := table.y8.map DigitAdaptor.unpack
  y10 := table.y10.map DigitAdaptor.unpack }

@[simp] theorem evaluateDigit_unpack_pack (windows : Nat → BitAdaptor.FixedKeyOracle)
    (table : Option (Vector BitAdaptor.Table coordinateBitCount)) (value : BaseField)
    (inputMac : CoordinateMac) :
    evaluateDigit windows (table.map (DigitAdaptor.unpack ∘ DigitAdaptor.pack))
        value inputMac =
      evaluateDigit windows table value inputMac := by
  cases table with
  | none => rfl
  | some rows => simp [evaluateDigit, Function.comp_def]

@[simp] theorem evaluate_unpack_pack (oracles : Oracles) (table : Table)
    (input : AffineInput) (inputMac : InputMac) :
    evaluate oracles table.pack.unpack input inputMac = evaluate oracles table input inputMac := by
  simp [evaluate, Table.pack, PackedTable.unpack]

/-- The Y row reads the same tables through the x-only cubic evaluator, so the
removed bits change that evaluation too. -/
@[simp] theorem evaluateY_unpack_pack (oracles : Oracles) (table : Table)
    (input : AffineInput) (inputMac : InputMac) :
    evaluateY oracles table.pack.unpack input inputMac =
      evaluateY oracles table input inputMac := by
  simp [evaluateY, Table.pack, PackedTable.unpack]

end Biquadratic

namespace FieldMacToECMac

/-- This is the transmitted point-MAC table. -/
structure PackedTable where
  x : Vector Biquadratic.PackedTable outputMacCount
  y : Vector Biquadratic.PackedTable outputMacCount
  z : Vector Biquadratic.PackedTable outputMacCount

def Table.pack (table : Table) : PackedTable := {
  x := table.x.map Biquadratic.Table.pack
  y := table.y.map Biquadratic.Table.pack
  z := table.z.map Biquadratic.Table.pack }

def PackedTable.unpack (table : PackedTable) : Table := {
  x := table.x.map Biquadratic.PackedTable.unpack
  y := table.y.map Biquadratic.PackedTable.unpack
  z := table.z.map Biquadratic.PackedTable.unpack }

@[simp] theorem evaluate_unpack_pack (table : Table) (oracles : Oracles)
    (input : AffineInput) (inputMac : InputMac) :
    evaluate table.pack.unpack oracles input inputMac = evaluate table oracles input inputMac := by
  simp only [evaluate, evaluateHomogeneous, Table.pack, PackedTable.unpack,
    Result.mk.injEq, true_and]
  apply Vector.ext
  intro index inRange
  simp [Vector.get, Biquadratic.evaluate_unpack_pack, Biquadratic.evaluateY_unpack_pack]

end FieldMacToECMac

namespace Pipeline

/-- This is the transmitted public table. -/
structure PackedTable where
  curve : CurveMembership.PackedTable
  pointMAC : FieldMacToECMac.PackedTable

def Table.pack (table : Table) : PackedTable := {
  curve := table.curve.pack
  pointMAC := table.pointMAC.pack }

def PackedTable.unpack (table : PackedTable) : Table := {
  curve := table.curve.unpack
  pointMAC := table.pointMAC.unpack }

/-- The removed bits change no evaluation. -/
@[simp] theorem evaluate_unpack_pack [FieldCertificate]
    (fixedKeyOracle : PermutationOracle FixedKeyIndex Cryptography.Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Cryptography.Block)
    (hashOracle : EncPRF.HashOracle) (table : Table)
    (input : BitInput) (inputMac : InputMac) :
    evaluate fixedKeyOracle encPRFOracle hashOracle table.pack.unpack input inputMac =
      evaluate fixedKeyOracle encPRFOracle hashOracle table input inputMac := by
  simp [evaluate, Table.pack, PackedTable.unpack]

end Pipeline

end Kriterion.ArgoMAC
