import Construction.Garbling
import Construction.ArgoMAC.BitPack
import Construction.ArgoMAC.Packed
import Encoding

namespace Kriterion.ArgoMAC

open BN254

-- The widest bit blob is two digit adaptors, 16,129 bytes, so the kernel walks
-- that many constructors when it checks a length.
set_option maxRecDepth 400000

namespace Wire

-- Lengths are read off the `encode` field alone. Unfolding a whole `Encoding`
-- instead drags its `decode_encode` proof into every goal, and the kernel then
-- rechecks that proof once per component of the 91-row table.
private theorem map_encode_length {α β : Type} (component : Encoding α)
    (forward : β → α) (backward : α → β)
    (inverse : ∀ value, backward (forward value) = value) (value : β) :
    ((component.map forward backward inverse).encode value).length =
      (component.encode (forward value)).length := rfl

private theorem pair_encode_length {α β : Type} (first : Encoding α)
    (second : Encoding β) (value : α × β) :
    ((first.pair second).encode value).length =
      (first.encode value.1).length + (second.encode value.2).length :=
  List.length_append

/-- This is one transmitted digit adaptor. -/
private abbrev Digits := Vector BitAdaptor.PackedTable coordinateBitCount

/-- A base field element occupies the `coordinateBitCount` bits its modulus
allows. Byte alignment would round that up to 256. -/
private def fieldPack : BitPack BaseField where
  width := coordinateBitCount
  toNat value := value.val
  ofNat value := value
  toNat_lt value := lt_trans value.val_lt (by decide)
  ofNat_toNat value := ZMod.natCast_zmod_val value

/-- One transmitted ciphertext row is exactly `coordinateBitCount` bits: the two
pad bits of a ciphertext carry no message and are not transmitted. -/
private def rowPack : BitPack BitAdaptor.PackedTable where
  width := coordinateBitCount
  toNat table := table.trueRow.toNat
  ofNat value := ⟨BitVec.ofNat coordinateBitCount value⟩
  toNat_lt table := table.trueRow.isLt
  ofNat_toNat table :=
    congrArg BitAdaptor.PackedTable.mk
      (BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt table.trueRow.isLt]))

/-- One digit adaptor is `coordinateBitCount` rows of `coordinateBitCount` bits,
packed with no padding between rows: 64,516 bits. -/
private def digitPack : BitPack Digits := rowPack.vector coordinateBitCount

/-- One digit adaptor is 64,516 bits in 8,065 bytes. Grouping two adaptors would
recover the four spare bits, but 8,065 bytes is already the largest blob whose
kernel cost this development can carry; see the note on `Submission`. -/
private def adaptor : Encoding Digits :=
  digitPack.encoding 8065 (by decide)

/-- The curve gadget publishes three masked coefficients. -/
private def curveCoefficients : Encoding (BaseField × BaseField × BaseField) :=
  (fieldPack.pair (fieldPack.pair fieldPack)).encoding 96 (by decide)

/-- The X and Z rows publish five masked coefficients: 1,270 bits in 159 bytes
rather than five separate 32-byte fields. -/
private def fiveCoefficients :
    Encoding (BaseField × BaseField × BaseField × BaseField × BaseField) :=
  (fieldPack.pair (fieldPack.pair (fieldPack.pair (fieldPack.pair fieldPack)))).encoding
    159 (by decide)

/-- The Y row publishes four masked coefficients: 1,016 bits in exactly 127 bytes. -/
private def fourCoefficients : Encoding (BaseField × BaseField × BaseField × BaseField) :=
  (fieldPack.pair (fieldPack.pair (fieldPack.pair fieldPack))).encoding 127 (by decide)

private theorem adaptor_length (value : Digits) :
    (adaptor.encode value).length = 8065 :=
  BitPack.encoding_length _ 8065 _ value

private theorem curveCoefficients_length (value : BaseField × BaseField × BaseField) :
    (curveCoefficients.encode value).length = 96 :=
  BitPack.encoding_length _ 96 _ value

private theorem fiveCoefficients_length
    (value : BaseField × BaseField × BaseField × BaseField × BaseField) :
    (fiveCoefficients.encode value).length = 159 :=
  BitPack.encoding_length _ 159 _ value

private theorem fourCoefficients_length
    (value : BaseField × BaseField × BaseField × BaseField) :
    (fourCoefficients.encode value).length = 127 :=
  BitPack.encoding_length _ 127 _ value

private def curve : Encoding CurveMembership.PackedTable :=
  (curveCoefficients.pair (adaptor.pair (adaptor.pair (adaptor.pair
    (adaptor.pair adaptor))))).map
    (fun value => ((value.c0, value.c1, value.c2),
      (value.x3, value.x5, value.x7, value.y4, value.y6)))
    (fun ⟨⟨c0, c1, c2⟩, x3, x5, x7, y4, y6⟩ => ⟨c0, c1, c2, x3, x5, x7, y4, y6⟩)
    (fun _ => rfl)

/-- The transmitted X row carries its nine filled slots and no presence tags. -/
private def xRow : Encoding Biquadratic.PackedXTable :=
  (fiveCoefficients.pair (adaptor.pair (adaptor.pair (adaptor.pair adaptor)))).map
    (fun value => ((value.c0, value.c1, value.c2, value.c3, value.c5),
      (value.x9, value.y6, value.y8, value.y10)))
    (fun ⟨⟨c0, c1, c2, c3, c5⟩, x9, y6, y8, y10⟩ =>
      ⟨c0, c1, c2, c3, c5, x9, y6, y8, y10⟩)
    (fun _ => rfl)

/-- The transmitted Y row carries its seven filled slots. -/
private def yRow : Encoding Biquadratic.PackedYTable :=
  (fourCoefficients.pair (adaptor.pair (adaptor.pair adaptor))).map
    (fun value => ((value.c0, value.c1, value.c4, value.c5),
      (value.x7, value.x9, value.y6)))
    (fun ⟨⟨c0, c1, c4, c5⟩, x7, x9, y6⟩ => ⟨c0, c1, c4, c5, x7, x9, y6⟩)
    (fun _ => rfl)

/-- The transmitted Z row carries its ten filled slots. -/
private def zRow : Encoding Biquadratic.PackedZTable :=
  (fiveCoefficients.pair (adaptor.pair (adaptor.pair (adaptor.pair
    (adaptor.pair adaptor))))).map
    (fun value => ((value.c0, value.c2, value.c3, value.c4, value.c5),
      (value.x7, value.x9, value.y6, value.y8, value.y10)))
    (fun ⟨⟨c0, c2, c3, c4, c5⟩, x7, x9, y6, y8, y10⟩ =>
      ⟨c0, c2, c3, c4, c5, x7, x9, y6, y8, y10⟩)
    (fun _ => rfl)

-- No `Encoding.map` may sit above an `Encoding.vector`: rewriting a length
-- through such a map unrolls the 91-row recursion, once per row, and the kernel
-- then rechecks the whole row encoding 91 times. The transmitted point-MAC and
-- pipeline types are plain products so that these two encodings need no map.
private def pointMAC : Encoding FieldMacToECMac.PackedTable :=
  (xRow.vector FieldMacToECMac.outputMacCount).pair
    ((yRow.vector FieldMacToECMac.outputMacCount).pair
      (zRow.vector FieldMacToECMac.outputMacCount))

/-- This is the identity on byte lists. It is defined by well-founded recursion,
so the kernel leaves it unevaluated.

That matters because the transmitted value no longer carries presence tags. A
tag is a `match` on a value the kernel cannot see through, and the baseline
encoding was full of them; without tags nothing stops the kernel from expanding
a ciphertext length check into an 8.8-million-element list literal. Every
statement about the encoding rewrites this away with `sealed_eq` first. -/
private def sealed (fuel : Nat) (bytes : List (Fin 256)) : List (Fin 256) :=
  if fuel = 0 then bytes else sealed (fuel - 1) bytes
termination_by fuel
decreasing_by omega

private theorem sealed_eq : ∀ (fuel : Nat) (bytes : List (Fin 256)), sealed fuel bytes = bytes
  | 0, bytes => by rw [sealed]; simp
  | fuel + 1, bytes => by rw [sealed]; simpa using sealed_eq fuel bytes

private def unsealed : Encoding Pipeline.PackedTable := curve.pair pointMAC

/-- This encoding includes every transmitted public field. Row identity is
statically known, so no field carries a presence tag. -/
def encoding : Encoding Pipeline.PackedTable where
  encode value := sealed 1 (unsealed.encode value)
  decode := unsealed.decode
  decode_encode value tail := by
    rw [sealed_eq]
    exact unsealed.decode_encode value tail

-- These stay `rw` chains rather than `simp` calls. `simp` matches its rewrite
-- rules up to reduction, which opens `BitPack.encoding` down to its
-- `Encoding.natural`, and the kernel then walks one constructor per byte.
private theorem curve_length (value : CurveMembership.PackedTable) :
    (curve.encode value).length = 40421 := by
  rw [curve, map_encode_length, pair_encode_length, pair_encode_length,
    pair_encode_length, pair_encode_length, pair_encode_length,
    curveCoefficients_length, adaptor_length, adaptor_length, adaptor_length,
    adaptor_length, adaptor_length]

private theorem xRow_length (value : Biquadratic.PackedXTable) :
    (xRow.encode value).length = 32419 := by
  rw [xRow, map_encode_length, pair_encode_length, pair_encode_length,
    pair_encode_length, pair_encode_length, fiveCoefficients_length,
    adaptor_length, adaptor_length, adaptor_length, adaptor_length]

private theorem yRow_length (value : Biquadratic.PackedYTable) :
    (yRow.encode value).length = 24322 := by
  rw [yRow, map_encode_length, pair_encode_length, pair_encode_length,
    pair_encode_length, fourCoefficients_length, adaptor_length,
    adaptor_length, adaptor_length]

private theorem zRow_length (value : Biquadratic.PackedZTable) :
    (zRow.encode value).length = 40484 := by
  rw [zRow, map_encode_length, pair_encode_length, pair_encode_length,
    pair_encode_length, pair_encode_length, pair_encode_length,
    fiveCoefficients_length, adaptor_length, adaptor_length, adaptor_length,
    adaptor_length, adaptor_length]

private theorem pointMAC_length (value : FieldMacToECMac.PackedTable) :
    (pointMAC.encode value).length = 8847475 := by
  rw [pointMAC, pair_encode_length, pair_encode_length,
    Encoding.vector_length xRow 32419 _ _ (fun _ => xRow_length _),
    Encoding.vector_length yRow 24322 _ _ (fun _ => yRow_length _),
    Encoding.vector_length zRow 40484 _ _ (fun _ => zRow_length _)]
  rfl

/-- Row identity fixes every transmitted slot, so the encoded length does not
depend on the value at all. -/
theorem encoding_length (value : Pipeline.PackedTable) :
    (encoding.encode value).length = 8887896 := by
  show (sealed 1 (unsealed.encode value)).length = 8887896
  rw [sealed_eq, unsealed, pair_encode_length, curve_length, pointMAC_length]

/-- Every scalar and random tape produces the same complete ciphertext length. -/
theorem garble_length (construction : Construction) (scalar : NonZeroScalar)
    (randomness : Garbling.Randomness) :
    (encoding.encode
      (Pipeline.Table.pack (Garbling.garble construction scalar randomness).1)).length =
      8887896 :=
  encoding_length _

end Wire
end Kriterion.ArgoMAC
