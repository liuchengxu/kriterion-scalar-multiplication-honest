import Proof.Privacy.Simulator.Arithmetic.PublicWire

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security
set_option maxRecDepth 100000
attribute [local irreducible] Encoding.natural Encoding.vector Wire.adaptor Wire.digitPack
  Wire.curve Wire.pointMAC Wire.encoding

/-- Each sampled X row has the canonical public length. -/
theorem publicXEncoded_length (sample : XPublicSample) :
    (Wire.xRow.encode sample.request.table.packX).length = 32419 :=
  Wire.xRow_length _

/-- Each sampled Y row has the canonical public length. -/
theorem publicYEncoded_length (sample : YPublicSample) :
    (Wire.yRow.encode sample.request.table.packY).length = 24322 :=
  Wire.yRow_length _

/-- Each sampled Z row has the canonical public length. -/
theorem publicZEncoded_length (sample : ZPublicSample) :
    (Wire.zRow.encode sample.request.table.packZ).length = 40484 :=
  Wire.zRow_length _

/-- Every sampled public table has exactly 8887896 canonical bytes. -/
theorem publicSourceTable_length (sample : PublicSample) :
    (Wire.encoding.encode (publicSourceTable sample)).length = 8887896 := by
  have sourceCurve : (publicSourceTable sample).1 = sample.curveRequest.table.pack := rfl
  have sourceX : (publicSourceTable sample).2.1 =
      (pointGateTable sample.pointRequests).x.map Biquadratic.Table.packX := rfl
  have sourceY : (publicSourceTable sample).2.2.1 =
      (pointGateTable sample.pointRequests).y.map Biquadratic.Table.packY := rfl
  have sourceZ : (publicSourceTable sample).2.2.2 =
      (pointGateTable sample.pointRequests).z.map Biquadratic.Table.packZ := rfl
  have xrow (index : Fin FieldMacToECMac.outputMacCount) :
      (Wire.xRow.encode
        (((pointGateTable sample.pointRequests).x.map Biquadratic.Table.packX).get index)).length =
        32419 := by
    rw [Vector.get_map, pointGateTable, Vector.get_ofFn, PublicSample.pointRequests, Vector.get_map]
    simpa only [BiquadraticRowRequest.table, RowPublicSample.request] using
      publicXEncoded_length (sample.points.get index).x
  have yrow (index : Fin FieldMacToECMac.outputMacCount) :
      (Wire.yRow.encode
        (((pointGateTable sample.pointRequests).y.map Biquadratic.Table.packY).get index)).length =
        24322 := by
    rw [Vector.get_map, pointGateTable, Vector.get_ofFn, PublicSample.pointRequests, Vector.get_map]
    simpa only [BiquadraticRowRequest.table, RowPublicSample.request] using
      publicYEncoded_length (sample.points.get index).y
  have zrow (index : Fin FieldMacToECMac.outputMacCount) :
      (Wire.zRow.encode
        (((pointGateTable sample.pointRequests).z.map Biquadratic.Table.packZ).get index)).length =
        40484 := by
    rw [Vector.get_map, pointGateTable, Vector.get_ofFn, PublicSample.pointRequests, Vector.get_map]
    simpa only [BiquadraticRowRequest.table, RowPublicSample.request] using
      publicZEncoded_length (sample.points.get index).z
  have x := Encoding.vector_length Wire.xRow 32419 FieldMacToECMac.outputMacCount
    ((pointGateTable sample.pointRequests).x.map Biquadratic.Table.packX) xrow
  have y := Encoding.vector_length Wire.yRow 24322 FieldMacToECMac.outputMacCount
    ((pointGateTable sample.pointRequests).y.map Biquadratic.Table.packY) yrow
  have z := Encoding.vector_length Wire.zRow 40484 FieldMacToECMac.outputMacCount
    ((pointGateTable sample.pointRequests).z.map Biquadratic.Table.packZ) zrow
  rw [Wire.encoding_bytes, Wire.unsealed, encodingPair_encode, Wire.pointMAC, encodingPair_encode,
    encodingPair_encode, sourceCurve, sourceX, sourceY, sourceZ,
    List.length_append, List.length_append, List.length_append, Wire.curve_length, x, y, z]
  norm_num

end Kriterion.ArgoMAC.ArithmeticSimulator
