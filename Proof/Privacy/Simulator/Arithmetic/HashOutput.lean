import Construction.Simulator.HashOutput
import Proof.Privacy.Simulator.Arithmetic.WordOutput
import Proof.Privacy.Simulator.Arithmetic.WireCodec
import Proof.Privacy.Simulator.SimulatorMachineLaw

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol

/-- Adjacent linear lists execute in their source order. -/
theorem executeLinear_append (first second : List LinearInstruction) (memory : Memory) :
    executeLinear (first ++ second) memory = executeLinear second (executeLinear first memory) := by
  exact List.foldl_append

/-- The shift uses two fixed instructions and changes no stored data. -/
theorem hashOutputShift_memory (memory : Memory) :
    executeLinear hashOutputShift memory =
      { memory with registers := (Function.update (Function.update memory.registers 9 128)
        8 (memory.registers 8 >>> 128)) } := by
  simp [executeLinear, hashOutputShift, LinearInstruction.execute, Arithmetic.eval]

/-- The shift preserves every RAM cell. -/
theorem hashOutputShift_ram (memory : Memory) :
    (executeLinear hashOutputShift memory).ram = memory.ram := by
  rw [hashOutputShift_memory]

/-- The two-block output uses 770 fixed instructions. -/
theorem hashOutput_length : hashOutput.length = 770 := by
  simp [hashOutput, hashOutputShift, wordOutput_length]

/-- The hash output puts the high block before the low block in the canonical wire. -/
theorem hashOutput_bits (memory : Memory) :
    (executeLinear hashOutput memory).bits 3 =
      bits 128 (memory.registers 8 >>> 128).toNat ++
        bits 128 (memory.registers 8).toNat ++ memory.bits 3 := by
  rw [hashOutput, executeLinear_append, executeLinear_append]
  change (executeLinear (wordOutput 128)
    (executeLinear hashOutputShift (executeLinear (wordOutput 128) memory))).bits 3 = _
  rw [wordOutput_bits 128 _ (by decide), hashOutputShift_memory]
  simp [wordOutput_source, wordOutput_bits 128 memory (by decide), wordOutput_protocol, List.append_assoc]

/-- The hash output preserves every stored table cell. -/
theorem hashOutput_ram (memory : Memory) : (executeLinear hashOutput memory).ram = memory.ram := by
  rw [hashOutput, executeLinear_append, executeLinear_append]
  change (executeLinear (wordOutput 128)
    (executeLinear hashOutputShift (executeLinear (wordOutput 128) memory))).ram = _
  rw [wordOutput_ram, hashOutputShift_ram, wordOutput_ram]

/-- The low-bit encoder is unchanged by reduction to its word width. -/
theorem bits_mod (width value : Nat) : bits width (value % 2 ^ width) = bits width value := by
  have same : BitVec.ofNat width (value % 2 ^ width) = BitVec.ofNat width value := by
    apply BitVec.eq_of_toNat_eq
    simp
  simp only [bits, same]

/-- The source hash conversion stores the first block in the high half. -/
theorem hashFin_decode (value : Word) :
    Security.SimulatorMachine.hashFin.symm value.toFin =
      (BitVec.ofNat 128 (value.toNat / 2 ^ 128), BitVec.ofNat 128 value.toNat) := by
  simp [Security.SimulatorMachine.hashFin, Security.SimulatorMachine.blockFin,
    finProdFinEquiv, BitVec.equivFin]
  have highBound : value.toNat / 2 ^ 128 < 2 ^ 128 := by
    apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
    simpa only [show 2 ^ 128 * 2 ^ 128 = 2 ^ 256 by norm_num] using value.isLt
  constructor
  · apply BitVec.eq_of_toNat_eq
    change value.toNat / 2 ^ 128 = (value.toNat / 2 ^ 128) % 2 ^ 128
    exact (Nat.mod_eq_of_lt highBound).symm
  · apply BitVec.eq_of_toNat_eq
    rfl

/-- The protocol parser accepts the complete packed hash answer in the correct block order. -/
theorem hashOutput_answer {FixedIndex EncIndex : Type} (input : BN254.BaseField) (memory : Memory)
    (empty : memory.bits 3 = []) :
    answer (PublicQuery.hash (FixedIndex := FixedIndex) (EncIndex := EncIndex) input)
      ((executeLinear hashOutput memory).bits 3) =
      some (Security.SimulatorMachine.hashFin.symm (memory.registers 8).toFin) := by
  rw [hashOutput_bits, empty, List.append_nil, hashFin_decode]
  have high : (memory.registers 8 >>> 128).toNat = (memory.registers 8).toNat / 2 ^ 128 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [high]
  have encoded := words_encoded 128 2
    #v[BitVec.ofNat 128 ((memory.registers 8).toNat / 2 ^ 128),
      BitVec.ofNat 128 (memory.registers 8).toNat]
  simp only [Vector.toList_mk, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    BitVec.toNat_ofNat, bits_mod] at encoded
  simp only [answer, encoded, Option.map_some]
  rfl

/-- The compiled hash output returns after 771 charged instructions. -/
theorem hashOutput_machine [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
    (input : BN254.BaseField) (memory : Memory) (empty : memory.bits 3 = []) :
    let machine := linearMachine hashOutput (by rw [hashOutput_length]; decide)
    (run machine (hashOutput.length + 1) ⟨⟨0, Nat.zero_lt_succ _⟩, memory⟩).map
      (fun result => result.bind fun result =>
        answer (PublicQuery.hash (FixedIndex := FixedIndex) (EncIndex := EncIndex) input)
          (result.1.memory.bits 3)) =
      PMF.pure (some (Security.SimulatorMachine.hashFin.symm (memory.registers 8).toFin)) := by
  dsimp only
  rw [linearMachine_run, PMF.pure_map]
  simp only [Option.bind_some]
  rw [hashOutput_answer (FixedIndex := FixedIndex) (EncIndex := EncIndex) input memory empty]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
