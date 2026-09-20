import Proof.Privacy.Simulator.Arithmetic.PublicRowWire

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security
set_option maxRecDepth 100000

/-- The fixed row schedule emits each encoded row in its array order. -/
theorem publicWire_rows {α : Type} (count : Nat) (encoding : Encoding α)
    (schedule : Nat → List WireSegment) (tables : Vector α count)
    (ram : Word → Word) (pointer : Word)
    (row : ∀ index : Fin count,
      (schedule index.val).flatMap (WireSegment.wire ram pointer) =
        (encoding.encode (tables.get index)).flatMap (fun byte => bits 8 byte.val)) :
    ((List.range count).flatMap schedule).flatMap (WireSegment.wire ram pointer) =
      ((encoding.vector count).encode tables).flatMap (fun byte => bits 8 byte.val) := by
  rw [vectorEncoding_encode, List.flatMap_assoc, List.flatMap_assoc]
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  apply List.ext_getElem
  · simp
  · intro index left right
    have inside : index < count := by simpa using left
    simp only [List.getElem_map, List.getElem_range]
    exact row ⟨index, inside⟩

/-- The public source table uses all curve, X, Y, and Z entries. -/
def publicSourceTable (sample : PublicSample) : Pipeline.PackedTable :=
  (sample.curveRequest.table.pack, FieldMacToECMac.Table.pack (pointGateTable sample.pointRequests))

/-- The fixed public schedule emits exactly the complete canonical ciphertext. -/
theorem publicWire_bits (sample : PublicSample) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer 1017 (publicSchedule.words sample)) :
    publicWire.flatMap (WireSegment.wire ram pointer) =
      (Wire.encoding.encode (publicSourceTable sample)).flatMap (fun byte => bits 8 byte.val) := by
  have x := publicWire_rows FieldMacToECMac.outputMacCount Wire.xRow publicXWire
      ((pointGateTable sample.pointRequests).x.map Biquadratic.Table.packX) ram pointer (by
    intro index
    rw [Vector.get_map, pointGateTable, Vector.get_ofFn, PublicSample.pointRequests,
      Vector.get_map]
    simpa only [pointGateTable, PublicSample.pointRequests, BiquadraticRowRequest.table,
      RowPublicSample.request] using
      publicXWire_bits (sample.points.get index) index.val ram pointer
        (public_row_words sample ram pointer index stored))
  have y := publicWire_rows FieldMacToECMac.outputMacCount Wire.yRow publicYWire
      ((pointGateTable sample.pointRequests).y.map Biquadratic.Table.packY) ram pointer (by
    intro index
    rw [Vector.get_map, pointGateTable, Vector.get_ofFn, PublicSample.pointRequests,
      Vector.get_map]
    simpa only [pointGateTable, PublicSample.pointRequests, BiquadraticRowRequest.table,
      RowPublicSample.request] using
      publicYWire_bits (sample.points.get index) index.val ram pointer
        (public_row_words sample ram pointer index stored))
  have z := publicWire_rows FieldMacToECMac.outputMacCount Wire.zRow publicZWire
      ((pointGateTable sample.pointRequests).z.map Biquadratic.Table.packZ) ram pointer (by
    intro index
    rw [Vector.get_map, pointGateTable, Vector.get_ofFn, PublicSample.pointRequests,
      Vector.get_map]
    simpa only [pointGateTable, PublicSample.pointRequests, BiquadraticRowRequest.table,
      RowPublicSample.request] using
      publicZWire_bits (sample.points.get index) index.val ram pointer
        (public_row_words sample ram pointer index stored))
  have sourceCurve : (publicSourceTable sample).1 = sample.curveRequest.table.pack := rfl
  have sourceX : (publicSourceTable sample).2.1 =
      (pointGateTable sample.pointRequests).x.map Biquadratic.Table.packX := rfl
  have sourceY : (publicSourceTable sample).2.2.1 =
      (pointGateTable sample.pointRequests).y.map Biquadratic.Table.packY := rfl
  have sourceZ : (publicSourceTable sample).2.2.2 =
      (pointGateTable sample.pointRequests).z.map Biquadratic.Table.packZ := rfl
  rw [publicWire, List.flatMap_append, List.flatMap_append, List.flatMap_append,
    publicCurveWire_bits sample ram pointer stored, x, y, z]
  rw [List.append_assoc, List.append_assoc]
  rw [Wire.encoding_bytes, Wire.unsealed, encodingPair_encode, Wire.pointMAC, encodingPair_encode,
    encodingPair_encode, sourceCurve, sourceX, sourceY, sourceZ,
    List.flatMap_append, List.flatMap_append, List.flatMap_append]

end Kriterion.ArgoMAC.ArithmeticSimulator
