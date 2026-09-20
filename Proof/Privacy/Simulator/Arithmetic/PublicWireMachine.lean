import Proof.Privacy.Simulator.Arithmetic.PublicWire

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security

/-- A digit emits its 254 ciphertext words and its four pad bits. -/
@[simp] theorem wireDigit_length (base : Nat) : (wireDigit base).length = 255 := by
  simp [wireDigit]

/-- A coefficient group emits one segment per coefficient. -/
theorem wireCoefficients_length (base count : Nat) : (wireCoefficients base count).length = count := by
  rw [wireCoefficients, List.length_map, List.length_finRange]

/-- A digit group emits one 255-segment digit per gate. -/
theorem wireDigits_length (base : Nat) (gates : List Nat) :
    (wireDigits base gates).length = 255 * gates.length := by
  induction gates with
  | nil => simp [wireDigits]
  | cons head tail ih =>
      rw [wireDigits, List.flatMap_cons, List.length_append, wireDigit_length]
      change 255 + (wireDigits base tail).length = 255 * (head :: tail).length
      rw [ih, List.length_cons]
      omega

/-- The curve wire contains three coefficients and five digit tables. -/
@[simp] theorem publicCurveWire_length : publicCurveWire.length = 1279 := by
  simp only [publicCurveWire, List.length_append, List.length_cons, List.length_nil,
    wireCoefficients_length, wireDigits_length]

@[simp] theorem publicXWire_length (row : Nat) : (publicXWire row).length = 1026 := by
  simp only [publicXWire, List.length_append, List.length_cons, List.length_nil,
    wireCoefficients_length, wireDigits_length]

@[simp] theorem publicYWire_length (row : Nat) : (publicYWire row).length = 769 := by
  simp only [publicYWire, List.length_append, List.length_cons, List.length_nil,
    wireCoefficients_length, wireDigits_length]

@[simp] theorem publicZWire_length (row : Nat) : (publicZWire row).length = 1281 := by
  simp only [publicZWire, List.length_append, List.length_cons, List.length_nil,
    wireCoefficients_length, wireDigits_length]

/-- The complete public wire has exactly 281195 fixed segments. -/
theorem publicWire_length : publicWire.length = 281195 := by
  simp only [publicWire, List.length_append, List.length_flatMap,
    publicCurveWire_length, publicXWire_length, publicYWire_length, publicZWire_length,
    FieldMacToECMac.outputMacCount]
  norm_num

attribute [local irreducible] publicWire wireSegmentsProgram

/-- The fixed serializer table fits the machine's address space. -/
theorem publicWire_fits : (wireSegmentsProgram publicWire).length < 2 ^ 256 := by
  have bound := wireSegments_length publicWire
  rw [publicWire_length] at bound
  exact lt_of_le_of_lt bound (by decide)

/-- The checked package keeps the large fixed program symbolic during type checking. -/
private noncomputable def publicWireProgramPackage :
    {program : List LinearInstruction // program = wireSegmentsProgram publicWire} :=
  Classical.choice ⟨⟨wireSegmentsProgram publicWire, rfl⟩⟩

noncomputable def publicWireProgram : List LinearInstruction := publicWireProgramPackage.val

theorem publicWireProgram_eq : publicWireProgram = wireSegmentsProgram publicWire :=
  publicWireProgramPackage.property

theorem publicWireProgram_fits : publicWireProgram.length < 2 ^ 256 := by
  rw [publicWireProgram_eq]
  exact publicWire_fits

/-- The serializer contains only fixed loads, arithmetic instructions, and bit writes. -/
noncomputable def publicWireMachine : Machine := linearMachine publicWireProgram publicWireProgram_fits

/-- The serializer returns the complete canonical public wire and retains source RAM. -/
theorem publicWireMachine_run [FieldCertificate] (coin : SimulatorSampling.OfflineCoin)
    (memory : Memory) (stored : WordsAt memory.ram (memory.registers 11) 0 (offlineSchedule.words coin)) :
    (run publicWireMachine (publicWireProgram.length + 1)
      ⟨⟨0, Nat.zero_lt_succ publicWireMachine.size⟩, memory⟩).map
      (Option.map fun result => (result.1.memory.bits 3, result.1.memory.ram, result.2)) =
      PMF.pure (some ((Wire.encoding.encode (publicSourceTable coin.1)).flatMap (fun byte => bits 8 byte.val) ++
        memory.bits 3, memory.ram, publicWireProgram.length + 1)) := by
  have bits := wireSegments_bits publicWire memory
  have saved := (wireSegments_preserves publicWire memory).1
  rw [← publicWireProgram_eq] at bits saved
  rw [publicWire_bits coin.1 memory.ram (memory.registers 11) (offline_public_words coin _ _ stored)] at bits
  unfold publicWireMachine
  rw [linearMachine_run, PMF.pure_map]
  simp only [Option.map_some, bits, Function.update_self, saved]

/-- The complete serializer pays for its table and all executed instructions. -/
theorem publicWireMachine_budget :
    publicWireMachine.size + 1 + (publicWireProgram.length + 1) ≤ 477065504 := by
  have bound : publicWireProgram.length ≤ 771 * publicWire.length := by
    rw [publicWireProgram_eq]
    exact wireSegments_length publicWire
  rw [publicWire_length] at bound
  change publicWireProgram.length + 1 + (publicWireProgram.length + 1) ≤ _
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
