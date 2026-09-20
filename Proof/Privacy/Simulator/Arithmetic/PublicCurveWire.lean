import Proof.Privacy.Simulator.Arithmetic.PublicLayout
import Proof.Privacy.Simulator.Arithmetic.PublicWireBlocks

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security
set_option maxRecDepth 100000

/-- The stored curve sample emits its complete canonical public table. -/
theorem publicCurveWire_bits (sample : PublicSample) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer 1017 (publicSchedule.words sample)) :
    publicCurveWire.flatMap (WireSegment.wire ram pointer) =
      (Wire.curve.encode sample.curveRequest.table.pack).flatMap (fun byte => bits 8 byte.val) := by
  have curve := public_curve_words sample ram pointer stored
  have coefficient (index : Fin 3) :
      ram (pointer + BitVec.ofNat 256 (publicCurveBase + 3810 + index.val)) =
        BitVec.ofNat 256 (sample.curve.coefficients index).val :=
    gateData_coefficient 3 5 _ ram pointer 834395 index curve
  have coefficientList (index : Fin 3) :
      (curveCoefficients (sample.curveRequest.table.pack)).get index =
        sample.curve.coefficients index := by
    fin_cases index <;> rfl
  have table (gate : Fin 5) (index : Fin coordinateBitCount) :
      ram (pointer + BitVec.ofNat 256 (publicCurveBase + 2540 + 254 * gate.val + index.val)) =
        ((sample.curve.tables gate).get index).trueRow :=
    gateData_table 3 5 _ ram pointer 834395 gate index curve
  have digits : ∀ gate ∈ [0, 1, 2, 3, 4], PayloadStored ram pointer
      (publicCurveBase + 2540 + coordinateBitCount * gate)
      (curveDigitAt (sample.curveRequest.table.pack) gate) := by
    intro gate member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · intro index
      exact payloadStored_row ram pointer _ (sample.curve.tables 0) index (table 0 index)
    · intro index
      exact payloadStored_row ram pointer _ (sample.curve.tables 1) index (table 1 index)
    · intro index
      exact payloadStored_row ram pointer _ (sample.curve.tables 2) index (table 2 index)
    · intro index
      exact payloadStored_row ram pointer _ (sample.curve.tables 3) index (table 3 index)
    · intro index
      exact payloadStored_row ram pointer _ (sample.curve.tables 4) index (table 4 index)
  have coefficients : (wireCoefficients (publicCurveBase + 3810) 3 ++ [wirePad 6]).flatMap
      (WireSegment.wire ram pointer) =
      (curveCoefficients (sample.curveRequest.table.pack)).flatMap
        (fun value => bits coordinateBitCount value.val) ++ bits 6 0 := by
    exact wireCoefficients_bits (publicCurveBase + 3810) 6
      (curveCoefficients (sample.curveRequest.table.pack)) ram pointer
      (fun index => by rw [coefficientList index]; exact coefficient index)
  have digitBlock : (wireDigits (publicCurveBase + 2540) [0, 1, 2, 3, 4]).flatMap
      (WireSegment.wire ram pointer) =
      ([0, 1, 2, 3, 4] : List Nat).flatMap (fun gate =>
        (curveDigitAt (sample.curveRequest.table.pack) gate).toList.reverse.flatMap
          (fun row => bits coordinateBitCount row.trueRow.toNat) ++ bits 4 0) :=
    wireDigits_bits (publicCurveBase + 2540) [0, 1, 2, 3, 4]
      (curveDigitAt (sample.curveRequest.table.pack)) ram pointer digits
  rw [show publicCurveWire = wireCoefficients (publicCurveBase + 3810) 3 ++ [wirePad 6] ++
      wireDigits (publicCurveBase + 2540) [0, 1, 2, 3, 4] from rfl, List.flatMap_append,
    coefficients, digitBlock]
  rw [Wire.curve, encodingMap_encode, encodingPair_encode, encodingPair_encode,
    encodingPair_encode, encodingPair_encode, encodingPair_encode]
  simp only [List.flatMap_append]
  rw [curveCoefficients_bytes, adaptor_bytes, adaptor_bytes, adaptor_bytes, adaptor_bytes,
    adaptor_bytes]
  rw [show (curveCoefficients (sample.curveRequest.table.pack)).flatMap
        (fun value => bits coordinateBitCount value.val) =
      bits coordinateBitCount (sample.curve.coefficients 0).val ++
        (bits coordinateBitCount (sample.curve.coefficients 1).val ++
        (bits coordinateBitCount (sample.curve.coefficients 2).val ++ [])) from rfl]
  rw [show ([0, 1, 2, 3, 4] : List Nat).flatMap (fun gate =>
        (curveDigitAt (sample.curveRequest.table.pack) gate).toList.reverse.flatMap
          (fun row => bits coordinateBitCount row.trueRow.toNat) ++ bits 4 0) =
      (((DigitAdaptor.pack (sample.curve.tables 0)).toList.reverse.flatMap
          (fun row => bits coordinateBitCount row.trueRow.toNat) ++ bits 4 0) ++
        (((DigitAdaptor.pack (sample.curve.tables 1)).toList.reverse.flatMap
          (fun row => bits coordinateBitCount row.trueRow.toNat) ++ bits 4 0) ++
        (((DigitAdaptor.pack (sample.curve.tables 2)).toList.reverse.flatMap
          (fun row => bits coordinateBitCount row.trueRow.toNat) ++ bits 4 0) ++
        (((DigitAdaptor.pack (sample.curve.tables 3)).toList.reverse.flatMap
          (fun row => bits coordinateBitCount row.trueRow.toNat) ++ bits 4 0) ++
        (((DigitAdaptor.pack (sample.curve.tables 4)).toList.reverse.flatMap
          (fun row => bits coordinateBitCount row.trueRow.toNat) ++ bits 4 0) ++ []))))) from rfl]
  simp only [List.append_nil]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
