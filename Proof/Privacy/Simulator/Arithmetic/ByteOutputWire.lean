import Proof.Privacy.Simulator.Arithmetic.ByteOutputBlock
import Proof.Privacy.Simulator.Arithmetic.WireCodec

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- RAM bytes produce the same canonical bits as the public byte vector. -/
theorem byteScan_encoded (count : Nat) (memory : Memory) (values : Vector (BitVec 8) count)
    (stored : ∀ index : Fin count,
      memory.ram (memory.registers 11 + BitVec.ofNat 256 index.val) =
        BitVec.ofNat 256 values[index.val].toNat)
    (empty : memory.bits 3 = []) :
    (byteScan count memory).bits 3 =
      values.toList.flatMap (fun value => GarbledCircuit.SimulatorProtocol.bits 8 value.toNat) := by
  rw [byteScan_bits, empty, List.append_nil]
  apply congrArg List.flatten
  apply List.ext_getElem
  · simp
  · intro index left right
    have valid : index < count := by simpa using left
    simp only [List.getElem_map, List.getElem_range, Vector.getElem_toList]
    rw [stored ⟨index, valid⟩, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_of_lt_of_le values[index].isLt (by decide : 2 ^ 8 ≤ 2 ^ 256))]

/-- The protocol accepts the public value that the RAM byte output encodes. -/
theorem byteOutput_publicValue [BN254.FieldCertificate] {Public : Type}
    (encoding : Encoding Public) (value : Public) (count : Nat)
    (memory : Memory) (values : Vector (BitVec 8) count)
    (represented : encoding.encode value = (values.map BitVec.toFin).toList)
    (stored : ∀ index : Fin count,
      memory.ram (memory.registers 11 + BitVec.ofNat 256 index.val) =
        BitVec.ofNat 256 values[index.val].toNat)
    (empty : memory.bits 3 = []) (fits : count < 2 ^ 256)
    (counter : memory.registers 12 = BitVec.ofNat 256 count) :
    (run byteOutput (28 * count + 3) ⟨0, memory⟩).map
      (fun result => result.bind fun result =>
        GarbledCircuit.SimulatorProtocol.publicValue encoding count (result.1.memory.bits 3)) =
      PMF.pure (some value) := by
  rw [byteOutput_run count memory fits counter, PMF.pure_map]
  change PMF.pure (GarbledCircuit.SimulatorProtocol.publicValue encoding count
    ((byteScan count (byteInitial memory)).bits 3)) = _
  rw [byteScan_encoded count (byteInitial memory) values
    (by simpa [byteInitial] using stored) (by simpa [byteInitial] using empty),
    publicValue_encoded encoding value count values represented]

end Kriterion.ArgoMAC.ArithmeticSimulator
