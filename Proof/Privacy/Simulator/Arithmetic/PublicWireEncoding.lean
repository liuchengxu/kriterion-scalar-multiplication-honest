import Construction.ArgoMAC.Encoding
import Proof.Privacy.Simulator.Arithmetic.EncodingBits
import Proof.Privacy.Simulator.Arithmetic.WireSegments

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
set_option maxRecDepth 100000

/-- The canonical bit list of a natural number depends only on its low bits. -/
theorem protocolBits_mod (width value : Nat) :
    bits width (value % 2 ^ width) = bits width value := by
  apply List.ext_getElem
  · simp [bits]
  · intro index left right
    have bound : index < width := by simpa [bits] using left
    rw [protocolBits_get _ _ _ bound, protocolBits_get _ _ _ bound]
    simpa only [decide_eq_true bound, Bool.true_and] using Nat.testBit_mod_two_pow value width index

/-- A narrower value reads the same low bits from its packed slot. -/
theorem protocolBits_low (width low high : Nat) (bound : low < 2 ^ width) :
    bits width (low + 2 ^ width * high) = bits width low := by
  rw [← protocolBits_mod width (low + 2 ^ width * high), Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt bound]

/-- A packed slot's width is the width of its first component. -/
theorem packedPair_div (width low high : Nat) (bound : low < 2 ^ width) :
    (low + 2 ^ width * high) / 2 ^ width = high := by
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos width), Nat.div_eq_of_lt bound, Nat.zero_add]

/-- A packed pair emits its first component and then its second. -/
theorem packedPair_bits (width low high : Nat) (bound : low < 2 ^ width) :
    bits (width + width) (low + 2 ^ width * high) = bits width low ++ bits width high := by
  rw [protocolBits_append width width (low + 2 ^ width * high),
    protocolBits_low width low high bound, packedPair_div width low high bound]

/-- The bits above a packed value are the zero pad that byte-aligns its group. -/
theorem protocolBits_pad (pad width value : Nat) (bound : value < 2 ^ width) :
    bits (width + pad) value = bits width value ++ bits pad 0 := by
  rw [protocolBits_append width pad value, Nat.div_eq_of_lt bound]

/-- A bit packing transmits the little-endian bits of its packed value. -/
theorem bitPack_bits {α : Type} (pack : BitPack α) (bytes : Nat)
    (fits : pack.width ≤ 8 * bytes) (value : α) :
    ((pack.encoding bytes fits).encode value).flatMap (fun byte => bits 8 byte.val) =
      bits (8 * bytes) (pack.toNat value) :=
  naturalEncoding_bits bytes ⟨pack.toNat value, _⟩

/-- A packed vector transmits its rows from the last index down: the last row
takes the low bits of the blob. -/
theorem bitPackVector_bits {α : Type} (pack : BitPack α) (count : Nat)
    (values : Vector α count) :
    bits (pack.width * count) (pack.vectorToNat count values) =
      values.toList.reverse.flatMap (fun value => bits pack.width (pack.toNat value)) := by
  induction count with
  | zero =>
      rw [show values = #v[] from Vector.eq_empty]
      simp [BitPack.vectorToNat, bits]
  | succ count ih =>
      rw [BitPack.vectorToNat]
      have split : pack.width * (count + 1) = pack.width + pack.width * count := by ring
      rw [split, protocolBits_append pack.width (pack.width * count) _,
        protocolBits_low pack.width _ _ (pack.toNat_lt _),
        packedPair_div pack.width _ _ (pack.toNat_lt _), ih values.pop]
      have rebuilt := congrArg
        (fun block : Vector α (count + 1) =>
          block.toList.reverse.flatMap (fun value => bits pack.width (pack.toNat value)))
        (Vector.push_pop_back values)
      rw [← rebuilt]
      simp only [Vector.toList_push, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- A vector lists its entries in index order. -/
theorem vectorToList_finRange {α : Type} {count : Nat} (values : Vector α count) :
    values.toList = (List.finRange count).map values.get := by
  apply List.ext_getElem
  · simp
  · intro index left right
    rw [List.getElem_map, List.getElem_finRange]
    rfl

/-- The packed value of a transmitted coefficient group: the first coefficient
takes the low bits. -/
def fieldChain : List BaseField → Nat
  | [] => 0
  | value :: rest => value.val + 2 ^ coordinateBitCount * fieldChain rest

/-- A coefficient group emits its coefficients in order and then its zero pad. -/
theorem fieldChain_bits (pad : Nat) (values : List BaseField) :
    bits (coordinateBitCount * values.length + pad) (fieldChain values) =
      values.flatMap (fun value => bits coordinateBitCount value.val) ++ bits pad 0 := by
  induction values with
  | nil => simp [fieldChain]
  | cons value rest ih =>
      have split : coordinateBitCount * (rest.length + 1) + pad =
          coordinateBitCount + (coordinateBitCount * rest.length + pad) := by ring
      have bound : value.val < 2 ^ coordinateBitCount :=
        lt_trans value.val_lt (by decide)
      rw [List.length_cons, split, fieldChain, protocolBits_append coordinateBitCount _ _,
        protocolBits_low coordinateBitCount value.val _ bound,
        packedPair_div coordinateBitCount value.val _ bound, ih]
      simp only [List.flatMap_cons, List.append_assoc]

/-- A ciphertext's transmitted payload carries the same bits as its low
`coordinateBitCount`. -/
theorem payload_bits (value : BitAdaptor.Ciphertext) :
    bits coordinateBitCount (BitAdaptor.payload value).toNat = bits coordinateBitCount value.toNat := by
  rw [BitAdaptor.payload, BitVec.toNat_setWidth]
  exact protocolBits_mod coordinateBitCount value.toNat

/-- A field's transmitted bits are the low bits of its canonical value. -/
theorem fieldBits_value (value : BaseField) :
    bits coordinateBitCount (BitVec.ofNat 256 value.val).toNat = bits coordinateBitCount value.val := by
  have fits : value.val < 2 ^ 256 := lt_trans value.val_lt (by decide)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

/-- The curve gadget's coefficient group: three fields, six pad bits. -/
theorem curveCoefficients_bits (fits : (Wire.fieldPack.pair (Wire.fieldPack.pair
      Wire.fieldPack)).width ≤ 8 * 96) (value : BaseField × BaseField × BaseField) :
    ((((Wire.fieldPack.pair (Wire.fieldPack.pair Wire.fieldPack)).encoding 96
      fits).encode value).flatMap (fun byte => bits 8 byte.val)) =
      bits (coordinateBitCount * 3 + 6) (fieldChain [value.1, value.2.1, value.2.2]) := by
  have raw := bitPack_bits (Wire.fieldPack.pair (Wire.fieldPack.pair Wire.fieldPack)) 96
    fits value
  refine raw.trans ?_
  have chain : (Wire.fieldPack.pair (Wire.fieldPack.pair Wire.fieldPack)).toNat value =
      fieldChain [value.1, value.2.1, value.2.2] := by
    simp [BitPack.pair, Wire.fieldPack, fieldChain, BitPack.map]
  rw [chain]
  rfl

/-- An X or Z row's coefficient group: five fields, two pad bits. -/
theorem fiveCoefficients_bits (fits : (Wire.fieldPack.pair (Wire.fieldPack.pair
      (Wire.fieldPack.pair (Wire.fieldPack.pair Wire.fieldPack)))).width ≤ 8 * 159)
    (value : BaseField × BaseField × BaseField × BaseField × BaseField) :
    ((((Wire.fieldPack.pair (Wire.fieldPack.pair (Wire.fieldPack.pair (Wire.fieldPack.pair
      Wire.fieldPack)))).encoding 159 fits).encode value).flatMap
      (fun byte => bits 8 byte.val)) =
      bits (coordinateBitCount * 5 + 2)
        (fieldChain [value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2]) := by
  have raw := bitPack_bits
    (Wire.fieldPack.pair (Wire.fieldPack.pair (Wire.fieldPack.pair (Wire.fieldPack.pair
      Wire.fieldPack)))) 159 fits value
  refine raw.trans ?_
  have chain : (Wire.fieldPack.pair (Wire.fieldPack.pair (Wire.fieldPack.pair
      (Wire.fieldPack.pair Wire.fieldPack)))).toNat value =
      fieldChain [value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2] := by
    simp [BitPack.pair, Wire.fieldPack, fieldChain, BitPack.map]
  rw [chain]
  rfl

/-- A Y row's coefficient group: four fields, exactly 127 bytes of payload. -/
theorem fourCoefficients_bits (fits : (Wire.fieldPack.pair (Wire.fieldPack.pair
      (Wire.fieldPack.pair Wire.fieldPack))).width ≤ 8 * 127)
    (value : BaseField × BaseField × BaseField × BaseField) :
    ((((Wire.fieldPack.pair (Wire.fieldPack.pair (Wire.fieldPack.pair Wire.fieldPack))).encoding 127
      fits).encode value).flatMap (fun byte => bits 8 byte.val)) =
      bits (coordinateBitCount * 4)
        (fieldChain [value.1, value.2.1, value.2.2.1, value.2.2.2]) := by
  have raw := bitPack_bits
    (Wire.fieldPack.pair (Wire.fieldPack.pair (Wire.fieldPack.pair Wire.fieldPack))) 127
    fits value
  refine raw.trans ?_
  have chain : (Wire.fieldPack.pair (Wire.fieldPack.pair (Wire.fieldPack.pair Wire.fieldPack))).toNat
      value = fieldChain [value.1, value.2.1, value.2.2.1, value.2.2.2] := by
    simp [BitPack.pair, Wire.fieldPack, fieldChain, BitPack.map]
  rw [chain]
  rfl

/-- One digit adaptor's payload transmits its rows from the last index down. -/
theorem digitPack_bits (values : Vector BitAdaptor.PackedTable coordinateBitCount) :
    bits (coordinateBitCount * coordinateBitCount) (Wire.digitPack.toNat values) =
      values.toList.reverse.flatMap (fun row => bits coordinateBitCount row.trueRow.toNat) :=
  (bitPackVector_bits Wire.rowPack coordinateBitCount values).trans (by rfl)

/-- One digit adaptor transmits its rows from the last index down and then the
four pad bits of its 8,065-byte blob. -/
theorem adaptor_bits (fits : Wire.digitPack.width ≤ 8 * 8065)
    (value : Vector BitAdaptor.PackedTable coordinateBitCount) :
    ((((Wire.digitPack).encoding 8065 fits).encode value).flatMap
      (fun byte => bits 8 byte.val)) =
      value.toList.reverse.flatMap (fun row => bits coordinateBitCount row.trueRow.toNat) ++
        bits 4 0 := by
  have raw := bitPack_bits Wire.digitPack 8065 fits value
  refine raw.trans ?_
  have split : 8 * 8065 = coordinateBitCount * coordinateBitCount + 4 := by decide
  rw [split, protocolBits_pad 4 (coordinateBitCount * coordinateBitCount) _
      (Wire.digitPack.toNat_lt value), digitPack_bits value]

/-- The curve gadget's coefficient bytes are its packed field chain and pad. -/
theorem curveCoefficients_bytes (value : BaseField × BaseField × BaseField) :
    (Wire.curveCoefficients.encode value).flatMap (fun byte => bits 8 byte.val) =
      [value.1, value.2.1, value.2.2].flatMap
        (fun field => bits coordinateBitCount field.val) ++ bits 6 0 :=
  (curveCoefficients_bits (by decide) value).trans
    (fieldChain_bits 6 [value.1, value.2.1, value.2.2])

/-- An X or Z row's coefficient bytes are its packed field chain and pad. -/
theorem fiveCoefficients_bytes
    (value : BaseField × BaseField × BaseField × BaseField × BaseField) :
    (Wire.fiveCoefficients.encode value).flatMap (fun byte => bits 8 byte.val) =
      [value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2].flatMap
        (fun field => bits coordinateBitCount field.val) ++ bits 2 0 :=
  (fiveCoefficients_bits (by decide) value).trans
    (fieldChain_bits 2 [value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2])

/-- A Y row's coefficient bytes are exactly its packed field chain: no pad. -/
theorem fourCoefficients_bytes (value : BaseField × BaseField × BaseField × BaseField) :
    (Wire.fourCoefficients.encode value).flatMap (fun byte => bits 8 byte.val) =
      [value.1, value.2.1, value.2.2.1, value.2.2.2].flatMap
        (fun field => bits coordinateBitCount field.val) :=
  (fourCoefficients_bits (by decide) value).trans
    (fieldChain_bits 0 [value.1, value.2.1, value.2.2.1, value.2.2.2])

/-- One transmitted digit adaptor's bytes are its rows and the four pad bits. -/
theorem adaptor_bytes (value : Vector BitAdaptor.PackedTable coordinateBitCount) :
    (Wire.adaptor.encode value).flatMap (fun byte => bits 8 byte.val) =
      value.toList.reverse.flatMap (fun row => bits coordinateBitCount row.trueRow.toNat) ++
        bits 4 0 :=
  adaptor_bits (by decide) value

end Kriterion.ArgoMAC.ArithmeticSimulator
