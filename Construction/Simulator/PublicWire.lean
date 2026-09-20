import Construction.ArgoMAC.FieldMacToECMac
import Construction.Simulator.WireSegments

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A transmitted field element and a transmitted ciphertext row alike occupy the
`coordinateBitCount` bits their representation allows. -/
def wireStored (offset : Nat) : WireSegment := .stored (BitVec.ofNat 256 offset)

/-- A transmitted group byte-aligns with a pad of zero bits. -/
def wirePad (width : Fin 8) : WireSegment := .zero width

/-- A coefficient group emits one payload per coefficient, in transmitted order. -/
def wireCoefficients (base : Nat) (count : Nat) : List WireSegment :=
  (List.finRange count).map fun index => wireStored (base + index.val)

/-- A digit table emits its 254 ciphertext rows and then the four zero bits that
byte-align its 8,065-byte blob. The packed encoder gives the last row the low
bits of the blob, so the table is transmitted from its last index down. -/
def wireDigit (base : Nat) : List WireSegment :=
  (List.finRange coordinateBitCount).reverse.map (fun index => wireStored (base + index.val)) ++
    [wirePad 4]

/-- A digit group emits the named tables in transmitted order. -/
def wireDigits (base : Nat) (gates : List Nat) : List WireSegment :=
  gates.flatMap fun gate => wireDigit (base + coordinateBitCount * gate)

/-- One transmitted point row follows its predecessor by 9,158 offline words:
the Z gate data, then Y, then X. -/
def publicRowBase (row : Nat) : Nat := 1017 + 9158 * row

/-- The curve gadget follows all 91 point rows, 9,158 words each. -/
def publicCurveBase : Nat := 1017 + 9158 * FieldMacToECMac.outputMacCount

/-- The curve gadget publishes three coefficients and five digit tables.
Its coefficients take 762 bits of a 96-byte group, so six pad bits follow. -/
def publicCurveWire : List WireSegment :=
  wireCoefficients (publicCurveBase + 3810) 3 ++ [wirePad 6] ++
    wireDigits (publicCurveBase + 2540) [0, 1, 2, 3, 4]

/-- The X row publishes five coefficients and four digit tables. Its
coefficients take 1,270 bits of a 159-byte group, so two pad bits follow. -/
def publicXWire (row : Nat) : List WireSegment :=
  let base := publicRowBase row
  wireCoefficients (base + 9153) 5 ++ [wirePad 2] ++ wireDigits (base + 8137) [3, 0, 1, 2]

/-- The Y row publishes four coefficients and three digit tables. Its
coefficients take 1,016 bits, which is exactly 127 bytes, so no pad follows. -/
def publicYWire (row : Nat) : List WireSegment :=
  let base := publicRowBase row
  wireCoefficients (base + 6101) 4 ++ wireDigits (base + 5339) [1, 2, 0]

/-- The Z row publishes five coefficients and five digit tables. -/
def publicZWire (row : Nat) : List WireSegment :=
  let base := publicRowBase row
  wireCoefficients (base + 3810) 5 ++ [wirePad 2] ++ wireDigits (base + 2540) [3, 4, 0, 1, 2]

/-- The public wire emits the curve gadget, then every X, Y, and Z row. -/
def publicWire : List WireSegment :=
  publicCurveWire ++ (List.range FieldMacToECMac.outputMacCount).flatMap publicXWire ++
    (List.range FieldMacToECMac.outputMacCount).flatMap publicYWire ++
      (List.range FieldMacToECMac.outputMacCount).flatMap publicZWire

end Kriterion.ArgoMAC.ArithmeticSimulator
