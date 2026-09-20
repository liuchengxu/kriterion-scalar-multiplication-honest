import Proof.Privacy.Simulator.Arithmetic.PublicCurveWire

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security
set_option maxRecDepth 100000

/-- The stored X row emits its complete canonical public table. -/
theorem publicXWire_bits (sample : RowPublicSample) (row : Nat) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer (publicRowBase row) (rowSchedule.words sample)) :
    (publicXWire row).flatMap (WireSegment.wire ram pointer) =
      (Wire.xRow.encode sample.x.request.table.packX).flatMap (fun byte => bits 8 byte.val) := by
  have source := row_x_words sample ram pointer (publicRowBase row) stored
  have coefficient (index : Fin 5) :
      ram (pointer + BitVec.ofNat 256 (publicRowBase row + 9153 + index.val)) =
        BitVec.ofNat 256 (sample.x.coefficients index).val :=
    gateData_coefficient 5 4 _ ram pointer (publicRowBase row + 6105) index source
  have coefficientList (index : Fin 5) :
      ([sample.x.coefficients 0, sample.x.coefficients 1, sample.x.coefficients 2,
        sample.x.coefficients 3, sample.x.coefficients 4].get index) =
        sample.x.coefficients index := by
    fin_cases index <;> rfl
  have table (gate : Fin 4) (index : Fin coordinateBitCount) :
      ram (pointer + BitVec.ofNat 256 (publicRowBase row + 8137 + 254 * gate.val + index.val)) =
        ((sample.x.tables gate).get index).trueRow :=
    gateData_table 5 4 _ ram pointer (publicRowBase row + 6105) gate index source
  have digits : ∀ gate ∈ [3, 0, 1, 2], PayloadStored ram pointer
      (publicRowBase row + 8137 + coordinateBitCount * gate)
      (xDigitAt (sample.x.request.table.packX) gate) := by
    intro gate member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · intro index
      exact payloadStored_row ram pointer _ (sample.x.tables 3) index (table 3 index)
    · intro index
      exact payloadStored_row ram pointer _ (sample.x.tables 0) index (table 0 index)
    · intro index
      exact payloadStored_row ram pointer _ (sample.x.tables 1) index (table 1 index)
    · intro index
      exact payloadStored_row ram pointer _ (sample.x.tables 2) index (table 2 index)
  have coefficients : (wireCoefficients (publicRowBase row + 9153) 5 ++ [wirePad 2]).flatMap
      (WireSegment.wire ram pointer) =
      [sample.x.coefficients 0, sample.x.coefficients 1, sample.x.coefficients 2,
        sample.x.coefficients 3, sample.x.coefficients 4].flatMap
        (fun value => bits coordinateBitCount value.val) ++ bits 2 0 :=
    wireCoefficients_bits (publicRowBase row + 9153) 2
      [sample.x.coefficients 0, sample.x.coefficients 1, sample.x.coefficients 2,
        sample.x.coefficients 3, sample.x.coefficients 4] ram pointer
      (fun index => by rw [coefficientList index]; exact coefficient index)
  have digitBlock : (wireDigits (publicRowBase row + 8137) [3, 0, 1, 2]).flatMap
      (WireSegment.wire ram pointer) =
      ([3, 0, 1, 2] : List Nat).flatMap (fun gate =>
        (xDigitAt (sample.x.request.table.packX) gate).toList.reverse.flatMap
          (fun row => bits coordinateBitCount row.trueRow.toNat) ++ bits 4 0) :=
    wireDigits_bits (publicRowBase row + 8137) [3, 0, 1, 2]
      (xDigitAt (sample.x.request.table.packX)) ram pointer digits
  rw [show publicXWire row = wireCoefficients (publicRowBase row + 9153) 5 ++ [wirePad 2] ++
      wireDigits (publicRowBase row + 8137) [3, 0, 1, 2] from rfl, List.flatMap_append,
    coefficients, digitBlock]
  rw [Wire.xRow, encodingMap_encode, encodingPair_encode, encodingPair_encode,
    encodingPair_encode, encodingPair_encode]
  simp only [List.flatMap_append]
  rw [fiveCoefficients_bytes, adaptor_bytes, adaptor_bytes, adaptor_bytes, adaptor_bytes]
  rw [flatMap_four (fun gate => (xDigitAt (sample.x.request.table.packX) gate).toList.reverse.flatMap
      (fun row => bits coordinateBitCount row.trueRow.toNat) ++ bits 4 0) 3 0 1 2]
  simp only [List.append_nil]
  rfl


/-- The stored Y row emits its complete canonical public table. -/
theorem publicYWire_bits (sample : RowPublicSample) (row : Nat) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer (publicRowBase row) (rowSchedule.words sample)) :
    (publicYWire row).flatMap (WireSegment.wire ram pointer) =
      (Wire.yRow.encode sample.y.request.table.packY).flatMap (fun byte => bits 8 byte.val) := by
  have source := row_y_words sample ram pointer (publicRowBase row) stored
  have coefficient (index : Fin 4) :
      ram (pointer + BitVec.ofNat 256 (publicRowBase row + 6101 + index.val)) =
        BitVec.ofNat 256 (sample.y.coefficients index).val :=
    gateData_coefficient 4 3 _ ram pointer (publicRowBase row + 3815) index source
  have coefficientList (index : Fin 4) :
      ([sample.y.coefficients 0, sample.y.coefficients 1, sample.y.coefficients 2,
        sample.y.coefficients 3].get index) =
        sample.y.coefficients index := by
    fin_cases index <;> rfl
  have table (gate : Fin 3) (index : Fin coordinateBitCount) :
      ram (pointer + BitVec.ofNat 256 (publicRowBase row + 5339 + 254 * gate.val + index.val)) =
        ((sample.y.tables gate).get index).trueRow :=
    gateData_table 4 3 _ ram pointer (publicRowBase row + 3815) gate index source
  have digits : ∀ gate ∈ [1, 2, 0], PayloadStored ram pointer
      (publicRowBase row + 5339 + coordinateBitCount * gate)
      (yDigitAt (sample.y.request.table.packY) gate) := by
    intro gate member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl
    · intro index
      exact payloadStored_row ram pointer _ (sample.y.tables 1) index (table 1 index)
    · intro index
      exact payloadStored_row ram pointer _ (sample.y.tables 2) index (table 2 index)
    · intro index
      exact payloadStored_row ram pointer _ (sample.y.tables 0) index (table 0 index)
  have coefficients : (wireCoefficients (publicRowBase row + 6101) 4).flatMap
      (WireSegment.wire ram pointer) =
      [sample.y.coefficients 0, sample.y.coefficients 1, sample.y.coefficients 2,
        sample.y.coefficients 3].flatMap (fun value => bits coordinateBitCount value.val) :=
    wireCoefficients_flatMap (publicRowBase row + 6101)
      [sample.y.coefficients 0, sample.y.coefficients 1, sample.y.coefficients 2,
        sample.y.coefficients 3] ram pointer
      (fun index => by rw [coefficientList index]; exact coefficient index)
  have digitBlock : (wireDigits (publicRowBase row + 5339) [1, 2, 0]).flatMap
      (WireSegment.wire ram pointer) =
      ([1, 2, 0] : List Nat).flatMap (fun gate =>
        (yDigitAt (sample.y.request.table.packY) gate).toList.reverse.flatMap
          (fun row => bits coordinateBitCount row.trueRow.toNat) ++ bits 4 0) :=
    wireDigits_bits (publicRowBase row + 5339) [1, 2, 0]
      (yDigitAt (sample.y.request.table.packY)) ram pointer digits
  rw [show publicYWire row = wireCoefficients (publicRowBase row + 6101) 4 ++
      wireDigits (publicRowBase row + 5339) [1, 2, 0] from rfl, List.flatMap_append,
    coefficients, digitBlock]
  rw [Wire.yRow, encodingMap_encode, encodingPair_encode, encodingPair_encode,
    encodingPair_encode]
  simp only [List.flatMap_append]
  rw [fourCoefficients_bytes, adaptor_bytes, adaptor_bytes, adaptor_bytes]
  rw [flatMap_three (fun gate => (yDigitAt (sample.y.request.table.packY) gate).toList.reverse.flatMap
      (fun row => bits coordinateBitCount row.trueRow.toNat) ++ bits 4 0) 1 2 0]
  simp only [List.append_nil]
  rfl


/-- The stored Z row emits its complete canonical public table. -/
theorem publicZWire_bits (sample : RowPublicSample) (row : Nat) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer (publicRowBase row) (rowSchedule.words sample)) :
    (publicZWire row).flatMap (WireSegment.wire ram pointer) =
      (Wire.zRow.encode sample.z.request.table.packZ).flatMap (fun byte => bits 8 byte.val) := by
  have source := row_z_words sample ram pointer (publicRowBase row) stored
  have coefficient (index : Fin 5) :
      ram (pointer + BitVec.ofNat 256 (publicRowBase row + 3810 + index.val)) =
        BitVec.ofNat 256 (sample.z.coefficients index).val :=
    gateData_coefficient 5 5 _ ram pointer (publicRowBase row + 0) index source
  have coefficientList (index : Fin 5) :
      ([sample.z.coefficients 0, sample.z.coefficients 1, sample.z.coefficients 2,
        sample.z.coefficients 3, sample.z.coefficients 4].get index) =
        sample.z.coefficients index := by
    fin_cases index <;> rfl
  have table (gate : Fin 5) (index : Fin coordinateBitCount) :
      ram (pointer + BitVec.ofNat 256 (publicRowBase row + 2540 + 254 * gate.val + index.val)) =
        ((sample.z.tables gate).get index).trueRow :=
    gateData_table 5 5 _ ram pointer (publicRowBase row + 0) gate index source
  have digits : ∀ gate ∈ [3, 4, 0, 1, 2], PayloadStored ram pointer
      (publicRowBase row + 2540 + coordinateBitCount * gate)
      (zDigitAt (sample.z.request.table.packZ) gate) := by
    intro gate member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · intro index
      exact payloadStored_row ram pointer _ (sample.z.tables 3) index (table 3 index)
    · intro index
      exact payloadStored_row ram pointer _ (sample.z.tables 4) index (table 4 index)
    · intro index
      exact payloadStored_row ram pointer _ (sample.z.tables 0) index (table 0 index)
    · intro index
      exact payloadStored_row ram pointer _ (sample.z.tables 1) index (table 1 index)
    · intro index
      exact payloadStored_row ram pointer _ (sample.z.tables 2) index (table 2 index)
  have coefficients : (wireCoefficients (publicRowBase row + 3810) 5 ++ [wirePad 2]).flatMap
      (WireSegment.wire ram pointer) =
      [sample.z.coefficients 0, sample.z.coefficients 1, sample.z.coefficients 2,
        sample.z.coefficients 3, sample.z.coefficients 4].flatMap
        (fun value => bits coordinateBitCount value.val) ++ bits 2 0 :=
    wireCoefficients_bits (publicRowBase row + 3810) 2
      [sample.z.coefficients 0, sample.z.coefficients 1, sample.z.coefficients 2,
        sample.z.coefficients 3, sample.z.coefficients 4] ram pointer
      (fun index => by rw [coefficientList index]; exact coefficient index)
  have digitBlock : (wireDigits (publicRowBase row + 2540) [3, 4, 0, 1, 2]).flatMap
      (WireSegment.wire ram pointer) =
      ([3, 4, 0, 1, 2] : List Nat).flatMap (fun gate =>
        (zDigitAt (sample.z.request.table.packZ) gate).toList.reverse.flatMap
          (fun row => bits coordinateBitCount row.trueRow.toNat) ++ bits 4 0) :=
    wireDigits_bits (publicRowBase row + 2540) [3, 4, 0, 1, 2]
      (zDigitAt (sample.z.request.table.packZ)) ram pointer digits
  rw [show publicZWire row = wireCoefficients (publicRowBase row + 3810) 5 ++ [wirePad 2] ++
      wireDigits (publicRowBase row + 2540) [3, 4, 0, 1, 2] from rfl, List.flatMap_append,
    coefficients, digitBlock]
  rw [Wire.zRow, encodingMap_encode, encodingPair_encode, encodingPair_encode,
    encodingPair_encode, encodingPair_encode, encodingPair_encode]
  simp only [List.flatMap_append]
  rw [fiveCoefficients_bytes, adaptor_bytes, adaptor_bytes, adaptor_bytes, adaptor_bytes,
    adaptor_bytes]
  rw [flatMap_five (fun gate => (zDigitAt (sample.z.request.table.packZ) gate).toList.reverse.flatMap
      (fun row => bits coordinateBitCount row.trueRow.toNat) ++ bits 4 0) 3 4 0 1 2]
  simp only [List.append_nil]
  rfl


end Kriterion.ArgoMAC.ArithmeticSimulator
