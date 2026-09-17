/-
This file defines the transmitted table. It has the shape of `Pipeline.Table`
with the two untransmitted pad bits removed from every ciphertext row, and with
one transmitted type per row coordinate: `garbleX`, `garbleY` and `garbleZ` each
fill a fixed set of slots, so a transmitted row carries those slots directly and
needs no per-slot presence tag.
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

/-- Packing is total, so an absent adaptor slot still needs a value. `unpack`
restores `none` in that slot, so no evaluator ever reads this placeholder. -/
def absentDigits : Vector BitAdaptor.PackedTable coordinateBitCount :=
  Vector.replicate coordinateBitCount ⟨0⟩

/-- This is the transmitted form of one adaptor slot. -/
def packDigits (table : Option (Vector BitAdaptor.Table coordinateBitCount)) :
    Vector BitAdaptor.PackedTable coordinateBitCount :=
  (table.map DigitAdaptor.pack).getD absentDigits

@[simp] theorem packDigits_some (rows : Vector BitAdaptor.Table coordinateBitCount) :
    packDigits (some rows) = DigitAdaptor.pack rows := rfl

@[simp] theorem evaluateDigit_some_unpack_pack (windows : Nat → BitAdaptor.FixedKeyOracle)
    (rows : Vector BitAdaptor.Table coordinateBitCount) (value : BaseField)
    (inputMac : CoordinateMac) :
    evaluateDigit windows (some (DigitAdaptor.unpack (DigitAdaptor.pack rows)))
        value inputMac =
      evaluateDigit windows (some rows) value inputMac := by
  simp [evaluateDigit]

/-- This is the transmitted X row. `garbleX` always leaves `c4` and `x7` absent,
and `evaluate` reads an absent coefficient as zero, so the transmitted row
carries the nine filled slots and no presence tags. -/
structure PackedXTable where
  c0 : BaseField
  c1 : BaseField
  c2 : BaseField
  c3 : BaseField
  c5 : BaseField
  x9 : Vector BitAdaptor.PackedTable coordinateBitCount
  y6 : Vector BitAdaptor.PackedTable coordinateBitCount
  y8 : Vector BitAdaptor.PackedTable coordinateBitCount
  y10 : Vector BitAdaptor.PackedTable coordinateBitCount

/-- This is the transmitted Y row. `garbleY` always leaves `c2`, `c3`, `y8` and
`y10` absent, and `evaluateY` reads none of them. -/
structure PackedYTable where
  c0 : BaseField
  c1 : BaseField
  c4 : BaseField
  c5 : BaseField
  x7 : Vector BitAdaptor.PackedTable coordinateBitCount
  x9 : Vector BitAdaptor.PackedTable coordinateBitCount
  y6 : Vector BitAdaptor.PackedTable coordinateBitCount

/-- This is the transmitted Z row. `garbleZ` always leaves `c1` absent. -/
structure PackedZTable where
  c0 : BaseField
  c2 : BaseField
  c3 : BaseField
  c4 : BaseField
  c5 : BaseField
  x7 : Vector BitAdaptor.PackedTable coordinateBitCount
  x9 : Vector BitAdaptor.PackedTable coordinateBitCount
  y6 : Vector BitAdaptor.PackedTable coordinateBitCount
  y8 : Vector BitAdaptor.PackedTable coordinateBitCount
  y10 : Vector BitAdaptor.PackedTable coordinateBitCount

def Table.packX (table : Table) : PackedXTable := {
  c0 := coefficient table.c0
  c1 := coefficient table.c1
  c2 := coefficient table.c2
  c3 := coefficient table.c3
  c5 := coefficient table.c5
  x9 := packDigits table.x9
  y6 := packDigits table.y6
  y8 := packDigits table.y8
  y10 := packDigits table.y10 }

def PackedXTable.unpack (table : PackedXTable) : Table := {
  c0 := some table.c0
  c1 := some table.c1
  c2 := some table.c2
  c3 := some table.c3
  c4 := none
  c5 := some table.c5
  x7 := none
  x9 := some (DigitAdaptor.unpack table.x9)
  y6 := some (DigitAdaptor.unpack table.y6)
  y8 := some (DigitAdaptor.unpack table.y8)
  y10 := some (DigitAdaptor.unpack table.y10) }

def Table.packY (table : Table) : PackedYTable := {
  c0 := coefficient table.c0
  c1 := coefficient table.c1
  c4 := coefficient table.c4
  c5 := coefficient table.c5
  x7 := packDigits table.x7
  x9 := packDigits table.x9
  y6 := packDigits table.y6 }

def PackedYTable.unpack (table : PackedYTable) : Table := {
  c0 := some table.c0
  c1 := some table.c1
  c2 := none
  c3 := none
  c4 := some table.c4
  c5 := some table.c5
  x7 := some (DigitAdaptor.unpack table.x7)
  x9 := some (DigitAdaptor.unpack table.x9)
  y6 := some (DigitAdaptor.unpack table.y6)
  y8 := none
  y10 := none }

def Table.packZ (table : Table) : PackedZTable := {
  c0 := coefficient table.c0
  c2 := coefficient table.c2
  c3 := coefficient table.c3
  c4 := coefficient table.c4
  c5 := coefficient table.c5
  x7 := packDigits table.x7
  x9 := packDigits table.x9
  y6 := packDigits table.y6
  y8 := packDigits table.y8
  y10 := packDigits table.y10 }

def PackedZTable.unpack (table : PackedZTable) : Table := {
  c0 := some table.c0
  c1 := none
  c2 := some table.c2
  c3 := some table.c3
  c4 := some table.c4
  c5 := some table.c5
  x7 := some (DigitAdaptor.unpack table.x7)
  x9 := some (DigitAdaptor.unpack table.x9)
  y6 := some (DigitAdaptor.unpack table.y6)
  y8 := some (DigitAdaptor.unpack table.y8)
  y10 := some (DigitAdaptor.unpack table.y10) }

/-- `garbleX` fills exactly the slots the transmitted X row carries, so the
restored row evaluates as the original. -/
@[simp] theorem evaluate_unpack_packX (oracles : Oracles) (c0 c1 c2 c3 c5 : BaseField)
    (randomness : XRandomness) (garbleOracles : Oracles) (inputKey : InputMacKey)
    (input : AffineInput) (inputMac : InputMac) :
    evaluate oracles
        (garbleX c0 c1 c2 c3 c5 randomness garbleOracles inputKey).packX.unpack
        input inputMac =
      evaluate oracles (garbleX c0 c1 c2 c3 c5 randomness garbleOracles inputKey)
        input inputMac := by
  simp [evaluate, garbleX, Table.packX, PackedXTable.unpack, coefficient]

/-- `garbleY` fills exactly the slots the transmitted Y row carries. The Y row
reads its tables through the x-only cubic evaluator. -/
@[simp] theorem evaluateY_unpack_packY (oracles : Oracles) (c0 c1 c4 c5 : BaseField)
    (randomness : YRandomness) (garbleOracles : Oracles) (inputKey : InputMacKey)
    (input : AffineInput) (inputMac : InputMac) :
    evaluateY oracles
        (garbleY c0 c1 c4 c5 randomness garbleOracles inputKey).packY.unpack
        input inputMac =
      evaluateY oracles (garbleY c0 c1 c4 c5 randomness garbleOracles inputKey)
        input inputMac := by
  simp [evaluateY, garbleY, Table.packY, PackedYTable.unpack, coefficient]

/-- `garbleZ` fills exactly the slots the transmitted Z row carries. -/
@[simp] theorem evaluate_unpack_packZ (oracles : Oracles) (c0 c2 c3 c4 c5 : BaseField)
    (randomness : ZRandomness) (garbleOracles : Oracles) (inputKey : InputMacKey)
    (input : AffineInput) (inputMac : InputMac) :
    evaluate oracles
        (garbleZ c0 c2 c3 c4 c5 randomness garbleOracles inputKey).packZ.unpack
        input inputMac =
      evaluate oracles (garbleZ c0 c2 c3 c4 c5 randomness garbleOracles inputKey)
        input inputMac := by
  simp [evaluate, garbleZ, Table.packZ, PackedZTable.unpack, coefficient]

end Biquadratic

namespace FieldMacToECMac

/-- This is the transmitted point-MAC table. Each coordinate carries its own
row shape, so no row transmits a presence tag. It is a plain product rather than
a structure: the encoding would otherwise need an `Encoding.map` above an
`Encoding.vector`, and checking a length through that map unrolls the 91-row
recursion in the kernel. -/
abbrev PackedTable :=
  Vector Biquadratic.PackedXTable outputMacCount ×
    Vector Biquadratic.PackedYTable outputMacCount ×
      Vector Biquadratic.PackedZTable outputMacCount

def Table.pack (table : Table) : PackedTable :=
  (table.x.map Biquadratic.Table.packX,
    table.y.map Biquadratic.Table.packY,
    table.z.map Biquadratic.Table.packZ)

def PackedTable.unpack (table : PackedTable) : Table := {
  x := table.1.map Biquadratic.PackedXTable.unpack
  y := table.2.1.map Biquadratic.PackedYTable.unpack
  z := table.2.2.map Biquadratic.PackedZTable.unpack }

/-- Every row of a garbled table has the fixed slot pattern of its coordinate,
so the transmitted table restores every field that evaluation reads. -/
@[simp] theorem evaluate_unpack_pack_garble (rows : Rows) (randomness : Randomness)
    (garbleOracles : Oracles) (inputKey : InputMacKey) (oracles : Oracles)
    (input : AffineInput) (inputMac : InputMac) :
    evaluate (PackedTable.unpack (Table.pack (garble rows randomness garbleOracles inputKey)))
        oracles input inputMac =
      evaluate (garble rows randomness garbleOracles inputKey) oracles input inputMac := by
  simp only [evaluate, evaluateHomogeneous, Table.pack, PackedTable.unpack,
    Result.mk.injEq, true_and]
  apply Vector.ext
  intro index inRange
  simp [Vector.get, garble, garbleRow]
  exact ⟨rfl, rfl, rfl⟩

end FieldMacToECMac

namespace Pipeline

/-- This is the transmitted public table, a plain product for the same reason
as `FieldMacToECMac.PackedTable`. -/
abbrev PackedTable := CurveMembership.PackedTable × FieldMacToECMac.PackedTable

def Table.pack (table : Table) : PackedTable :=
  (table.curve.pack, FieldMacToECMac.Table.pack table.pointMAC)

def PackedTable.unpack (table : PackedTable) : Table := {
  curve := table.1.unpack
  pointMAC := FieldMacToECMac.PackedTable.unpack table.2 }

/-- Neither the removed pad bits nor the dropped presence tags change any
evaluation of a garbled point-MAC table. The curve gadget already has one fixed
shape, so its part is arbitrary here. -/
@[simp] theorem evaluate_unpack_pack_garble [FieldCertificate]
    (fixedKeyOracle : PermutationOracle FixedKeyIndex Cryptography.Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Cryptography.Block)
    (hashOracle : EncPRF.HashOracle) (curve : CurveMembership.Table)
    (rows : FieldMacToECMac.Rows) (randomness : FieldMacToECMac.Randomness)
    (garbleOracles : FieldMacToECMac.Oracles) (inputKey : InputMacKey)
    (input : BitInput) (inputMac : InputMac) :
    evaluate fixedKeyOracle encPRFOracle hashOracle
        (PackedTable.unpack
          (Table.pack ⟨curve, FieldMacToECMac.garble rows randomness garbleOracles inputKey⟩))
        input inputMac =
      evaluate fixedKeyOracle encPRFOracle hashOracle
        ⟨curve, FieldMacToECMac.garble rows randomness garbleOracles inputKey⟩
        input inputMac := by
  simp [evaluate, Table.pack, PackedTable.unpack]

end Pipeline

end Kriterion.ArgoMAC
