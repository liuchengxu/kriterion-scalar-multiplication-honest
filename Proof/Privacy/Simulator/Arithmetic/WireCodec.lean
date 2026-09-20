import Security.AdaptivePrivacy

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open GarbledCircuit.SimulatorProtocol

/-- The protocol fold is the natural value of a little-endian bit vector. -/
theorem foldBits_value (source : List Bool) :
    source.foldr (fun bit acc => bit.toNat + 2 * acc) 0 =
      (BitVec.ofBoolListLE source).toNat := by
  induction source with
  | nil => rfl
  | cons bit source ih =>
      simp only [List.foldr_cons, BitVec.ofBoolListLE, BitVec.toNat_concat, ih]
      omega

/-- The canonical bit encoding retains exactly the requested low bits. -/
theorem bits_value (width value : Nat) :
    (bits width value).foldr (fun bit acc => bit.toNat + 2 * acc) 0 = value % 2 ^ width := by
  rw [foldBits_value]
  apply Nat.eq_of_testBit_eq
  intro index
  change (BitVec.ofBoolListLE (bits width value)).getLsbD index = _
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
  by_cases inside : index < width
  · simp [bits, List.getElem?_eq_getElem, inside, BitVec.getLsb, BitVec.getLsbD]
  · have outside : (bits width value)[index]? = none := by
      apply List.getElem?_eq_none
      simpa [bits] using Nat.le_of_not_gt inside
    rw [outside]
    simp [Nat.testBit_mod_two_pow, inside]

/-- Every encoded word contributes the same number of bits. -/
theorem encodedWords_length (width : Nat) (values : List (BitVec width)) :
    (values.flatMap (fun value => bits width value.toNat)).length = width * values.length := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, ih]
      have length : (bits width value.toNat).length = width := by simp [bits]
      rw [length, Nat.mul_succ, Nat.add_comm]

/-- The parser's offset selects exactly one encoded word. -/
theorem encodedWords_chunk (width : Nat) (values : List (BitVec width))
    (index : Nat) (valid : index < values.length) :
    ((values.flatMap (fun value => bits width value.toNat)).drop (width * index)).take width =
      bits width values[index].toNat := by
  induction values generalizing index with
  | nil => simp at valid
  | cons value values ih =>
      cases index with
      | zero =>
          simp only [Nat.mul_zero, List.drop_zero, List.flatMap_cons, List.getElem_cons_zero]
          exact List.take_left' (by simp [bits])
      | succ index =>
          have length : (bits width value.toNat).length = width := by simp [bits]
          rw [List.flatMap_cons, show width * (index + 1) = width + width * index by rw [Nat.mul_succ, Nat.add_comm],
            ← List.drop_drop, List.drop_left' length]
          exact ih index (by simpa using Nat.lt_of_succ_lt_succ valid)

/-- The protocol parser recovers every encoded word, including zero-width words. -/
theorem words_encoded (width count : Nat) (values : Vector (BitVec width) count) :
    words width count (values.toList.flatMap (fun value => bits width value.toNat)) = some values := by
  have length : (values.toList.flatMap (fun value => bits width value.toNat)).length = width * count := by
    simpa using encodedWords_length width values.toList
  rw [words, if_pos length]
  apply congrArg some
  apply Vector.ext
  intro index valid
  simp only [Vector.getElem_ofFn]
  rw [Nat.mul_comm index width, encodedWords_chunk width values.toList index (by simpa using valid), bits_value]
  simp [Nat.mod_eq_of_lt (values[index].isLt)]

/-- Canonical public bytes recover their encoded public value. -/
theorem publicValue_encoded {Public : Type} (encoding : Encoding Public)
    (value : Public) (count : Nat) (values : Vector (BitVec 8) count)
    (represented : encoding.encode value = (values.map BitVec.toFin).toList) :
    publicValue encoding count (values.toList.flatMap (fun byte => bits 8 byte.toNat)) =
      some value := by
  have decoded : encoding.decode (values.map BitVec.toFin).toList = some (value, []) := by
    rw [← represented]
    simpa using encoding.decode_encode value []
  unfold publicValue
  rw [words_encoded]
  change ((encoding.decode (values.map BitVec.toFin).toList).bind fun result =>
    if result.2.isEmpty && encoding.encode result.1 == (values.map BitVec.toFin).toList then
      some result.1 else none) = some value
  rw [decoded]
  simp [represented]

end Kriterion.ArgoMAC.ArithmeticSimulator
