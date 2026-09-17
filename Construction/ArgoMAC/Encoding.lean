import Construction.Garbling
import Construction.ArgoMAC.Packed
import Encoding

namespace Kriterion.ArgoMAC

open BN254

-- One packed digit adaptor is 8,065 bytes, so the kernel walks that many
-- constructors when it checks a length.
set_option maxRecDepth 100000

namespace Wire

private def field : Encoding BaseField :=
  (Encoding.natural 32).map
    (fun value => ⟨value.val, lt_trans value.val_lt (by decide)⟩)
    (fun value => value.val)
    (fun value => ZMod.natCast_zmod_val value)

/-- One digit adaptor is `coordinateBitCount` rows of `coordinateBitCount` bits.
The rows are packed with no per-row padding, so only the last byte of the
adaptor is partly unused. -/
private def digitBytes : Nat := 8065

private def rowsValue : (count : Nat) → Vector BitAdaptor.PackedTable count → Nat
  | 0, _ => 0
  | count + 1, rows =>
      rows.back.trueRow.toNat + 2 ^ coordinateBitCount * rowsValue count rows.pop

private def rowsVector : (count : Nat) → Nat → Vector BitAdaptor.PackedTable count
  | 0, _ => #v[]
  | count + 1, value =>
      (rowsVector count (value / 2 ^ coordinateBitCount)).push
        ⟨BitVec.ofNat coordinateBitCount value⟩

private theorem rowsVector_rowsValue (count : Nat)
    (rows : Vector BitAdaptor.PackedTable count) :
    rowsVector count (rowsValue count rows) = rows := by
  induction count with
  | zero =>
      apply Vector.ext
      intro index inRange
      exact absurd inRange (by omega)
  | succ count inductionHypothesis =>
      have positive : 0 < 2 ^ coordinateBitCount := by positivity
      have bound : rows.back.trueRow.toNat < 2 ^ coordinateBitCount := rows.back.trueRow.isLt
      have quotient : rowsValue (count + 1) rows / 2 ^ coordinateBitCount =
          rowsValue count rows.pop := by
        simp only [rowsValue]
        rw [Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt bound, Nat.zero_add]
      have remainder : rowsValue (count + 1) rows % 2 ^ coordinateBitCount =
          rows.back.trueRow.toNat := by
        simp only [rowsValue]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bound]
      show (rowsVector count (rowsValue (count + 1) rows / 2 ^ coordinateBitCount)).push
        ⟨BitVec.ofNat coordinateBitCount (rowsValue (count + 1) rows)⟩ = rows
      rw [quotient, inductionHypothesis rows.pop]
      rw [show (⟨BitVec.ofNat coordinateBitCount (rowsValue (count + 1) rows)⟩ :
          BitAdaptor.PackedTable) = rows.back by
        have values : (BitVec.ofNat coordinateBitCount
            (rowsValue (count + 1) rows)).toNat = rows.back.trueRow.toNat := by
          rw [BitVec.toNat_ofNat, remainder]
        exact congrArg BitAdaptor.PackedTable.mk (BitVec.eq_of_toNat_eq values)]
      exact Vector.push_pop_back rows

private theorem rowsValue_lt (count : Nat) (rows : Vector BitAdaptor.PackedTable count) :
    rowsValue count rows < (2 ^ coordinateBitCount) ^ count := by
  induction count with
  | zero => simp [rowsValue]
  | succ count inductionHypothesis =>
      have bound : rows.back.trueRow.toNat < 2 ^ coordinateBitCount := rows.back.trueRow.isLt
      have tail := inductionHypothesis rows.pop
      calc rowsValue (count + 1) rows
          = rows.back.trueRow.toNat + 2 ^ coordinateBitCount * rowsValue count rows.pop := rfl
        _ < 2 ^ coordinateBitCount * (rowsValue count rows.pop + 1) := by
            rw [Nat.mul_add, Nat.mul_one]; omega
        _ ≤ 2 ^ coordinateBitCount * (2 ^ coordinateBitCount) ^ count :=
            Nat.mul_le_mul_left _ tail
        _ = (2 ^ coordinateBitCount) ^ (count + 1) := by ring

private theorem rowsValue_lt_bytes (rows : Vector BitAdaptor.PackedTable coordinateBitCount) :
    rowsValue coordinateBitCount rows < 256 ^ digitBytes := by
  refine lt_of_lt_of_le (rowsValue_lt coordinateBitCount rows) ?_
  rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num [coordinateBitCount, digitBytes])

private def digit : Encoding (Vector BitAdaptor.PackedTable coordinateBitCount) :=
  (Encoding.natural digitBytes).map
    (fun rows => ⟨rowsValue coordinateBitCount rows, rowsValue_lt_bytes rows⟩)
    (fun value => rowsVector coordinateBitCount value.val)
    (fun rows => rowsVector_rowsValue coordinateBitCount rows)

private def curve : Encoding CurveMembership.PackedTable :=
  (field.pair (field.pair (field.pair
    (digit.pair (digit.pair (digit.pair (digit.pair digit))))))).map
    (fun value => (value.c0, value.c1, value.c2,
      value.x3, value.x5, value.x7, value.y4, value.y6))
    (fun ⟨c0, c1, c2, x3, x5, x7, y4, y6⟩ => ⟨c0, c1, c2, x3, x5, x7, y4, y6⟩)
    (fun _ => rfl)

private def biquadratic : Encoding Biquadratic.PackedTable :=
  let coefficient := field.option
  let rows := digit.option
  (coefficient.pair (coefficient.pair (coefficient.pair (coefficient.pair
    (coefficient.pair (coefficient.pair
      (rows.pair (rows.pair (rows.pair (rows.pair rows)))))))))).map
    (fun value => (value.c0, value.c1, value.c2, value.c3, value.c4, value.c5,
      value.x7, value.x9, value.y6, value.y8, value.y10))
    (fun ⟨c0, c1, c2, c3, c4, c5, x7, x9, y6, y8, y10⟩ =>
      ⟨c0, c1, c2, c3, c4, c5, x7, x9, y6, y8, y10⟩)
    (fun _ => rfl)

private def pointMAC : Encoding FieldMacToECMac.PackedTable :=
  let rows := biquadratic.vector FieldMacToECMac.outputMacCount
  (rows.pair (rows.pair rows)).map
    (fun value => (value.x, value.y, value.z))
    (fun ⟨x, y, z⟩ => ⟨x, y, z⟩)
    (fun _ => rfl)

/-- This encoding includes every public field and each optional-field tag. -/
def encoding : Encoding Pipeline.PackedTable :=
  (curve.pair pointMAC).map
    (fun value => (value.curve, value.pointMAC))
    (fun ⟨curve, pointMAC⟩ => ⟨curve, pointMAC⟩)
    (fun _ => rfl)

@[simp] private theorem field_length (value : BaseField) :
    (field.encode value).length = 32 := by simp [field, Encoding.map]

@[simp] private theorem digit_length (value : Vector BitAdaptor.PackedTable coordinateBitCount) :
    (digit.encode value).length = 8065 :=
  Encoding.natural_length digitBytes _

@[simp] private theorem curve_length (value : CurveMembership.PackedTable) :
    (curve.encode value).length = 40421 := by
  simp [curve, Encoding.map, Encoding.pair]

@[simp] private theorem coefficient_length (value : Option BaseField) :
    (field.option.encode value).length = if value.isSome then 33 else 1 := by
  cases value <;> simp [Encoding.option]

@[simp] private theorem rows_length
    (value : Option (Vector BitAdaptor.PackedTable coordinateBitCount)) :
    (digit.option.encode value).length = if value.isSome then 8066 else 1 := by
  cases value <;> simp [Encoding.option]

private theorem biquadratic_length (value : Biquadratic.PackedTable) :
    (biquadratic.encode value).length =
      (if value.c0.isSome then 33 else 1) + ((if value.c1.isSome then 33 else 1) +
      ((if value.c2.isSome then 33 else 1) + ((if value.c3.isSome then 33 else 1) +
      ((if value.c4.isSome then 33 else 1) + ((if value.c5.isSome then 33 else 1) +
      ((if value.x7.isSome then 8066 else 1) + ((if value.x9.isSome then 8066 else 1) +
      ((if value.y6.isSome then 8066 else 1) + ((if value.y8.isSome then 8066 else 1) +
      (if value.y10.isSome then 8066 else 1)))))))))) := by
  simp [biquadratic, Encoding.map, Encoding.pair]

@[simp] private theorem x_length (c0 c1 c2 c3 c5 : BaseField)
    (randomness : Biquadratic.XRandomness) (oracles : Biquadratic.Oracles) (key : InputMacKey) :
    (biquadratic.encode
      (Biquadratic.garbleX c0 c1 c2 c3 c5 randomness oracles key).pack).length = 32431 := by
  rw [biquadratic_length]
  simp [Biquadratic.garbleX, Biquadratic.Table.pack]

@[simp] private theorem y_length (c0 c1 c4 c5 : BaseField)
    (randomness : Biquadratic.YRandomness) (oracles : Biquadratic.Oracles) (key : InputMacKey) :
    (biquadratic.encode
      (Biquadratic.garbleY c0 c1 c4 c5 randomness oracles key).pack).length = 24334 := by
  rw [biquadratic_length]
  simp [Biquadratic.garbleY, Biquadratic.Table.pack]

@[simp] private theorem z_length (c0 c2 c3 c4 c5 : BaseField)
    (randomness : Biquadratic.ZRandomness) (oracles : Biquadratic.Oracles) (key : InputMacKey) :
    (biquadratic.encode
      (Biquadratic.garbleZ c0 c2 c3 c4 c5 randomness oracles key).pack).length = 40496 := by
  rw [biquadratic_length]
  simp [Biquadratic.garbleZ, Biquadratic.Table.pack]

private theorem pointMAC_length (rows : FieldMacToECMac.Rows)
    (randomness : FieldMacToECMac.Randomness) (oracles : FieldMacToECMac.Oracles) (key : InputMacKey) :
    (pointMAC.encode
      (FieldMacToECMac.garble rows randomness oracles key).pack).length = 8850751 := by
  simp only [pointMAC, Encoding.map, Encoding.pair, List.length_append,
    FieldMacToECMac.Table.pack]
  rw [Encoding.vector_length biquadratic 32431 _ _ (by
        intro index; simp [FieldMacToECMac.garble, FieldMacToECMac.garbleRow, Vector.get]),
      Encoding.vector_length biquadratic 24334 _ _ (by
        intro index; simp [FieldMacToECMac.garble, FieldMacToECMac.garbleRow, Vector.get]),
      Encoding.vector_length biquadratic 40496 _ _ (by
        intro index; simp [FieldMacToECMac.garble, FieldMacToECMac.garbleRow, Vector.get])]
  rfl

/-- Every scalar and random tape produces the same complete ciphertext length. -/
theorem garble_length (construction : Construction) (scalar : NonZeroScalar)
    (randomness : Garbling.Randomness) :
    (encoding.encode (Garbling.garble construction scalar randomness).1.pack).length = 8891172 := by
  simp [encoding, Encoding.map, Encoding.pair, Garbling.garble, Pipeline.garble,
    Pipeline.Table.pack, pointMAC_length]

end Wire
end Kriterion.ArgoMAC
