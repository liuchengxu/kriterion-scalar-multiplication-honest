import Proof.Privacy.Simulator.Arithmetic.PublicWireMachine
import Proof.Privacy.Simulator.Arithmetic.PublicWireLength
import Proof.Privacy.Simulator.Arithmetic.CanonicalPublic

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security
attribute [local irreducible] Wire.encoding publicValue words run
  publicWire wireSegmentsProgram

/-- The fixed program produces the complete public wire before it returns to a host. -/
theorem publicWireProgram_bits (coin : SimulatorSampling.OfflineCoin) (memory : Memory)
    (stored : WordsAt memory.ram (memory.registers 11) 0 (offlineSchedule.words coin)) :
    (executeLinear publicWireProgram memory).bits = Function.update memory.bits 3
      ((Wire.encoding.encode (publicSourceTable coin.1)).flatMap (fun byte => bits 8 byte.val) ++ memory.bits 3) := by
  have result := wireSegments_bits publicWire memory
  rw [← publicWireProgram_eq,
    publicWire_bits coin.1 memory.ram (memory.registers 11) (offline_public_words coin _ _ stored)] at result
  exact result

/-- The protocol accepts exactly the table that the offline source supplies. -/
theorem publicWireMachine_protocol [FieldCertificate] (coin : SimulatorSampling.OfflineCoin)
    (memory : Memory) (stored : WordsAt memory.ram (memory.registers 11) 0 (offlineSchedule.words coin))
    (empty : memory.bits 3 = []) :
    (run publicWireMachine (publicWireProgram.length + 1)
      ⟨⟨0, Nat.zero_lt_succ publicWireMachine.size⟩, memory⟩).map
      (fun result => result.bind fun result =>
        publicValue Wire.encoding 8887896 (result.1.memory.bits 3)) =
      PMF.pure (some (publicSourceTable coin.1)) := by
  apply parse_mapped_output
    (run publicWireMachine (publicWireProgram.length + 1)
      ⟨⟨0, Nat.zero_lt_succ publicWireMachine.size⟩, memory⟩)
    (fun result : Configuration (publicWireMachine.size + 1) × Nat => (result.1.memory.bits 3, result.1.memory.ram, result.2))
    (fun result : List Bool × (Word → Word) × Nat => publicValue Wire.encoding 8887896 result.1)
    _ _ (publicWireMachine_run coin memory stored)
  rw [empty, List.append_nil]
  exact publicValue_bytes Wire.encoding (publicSourceTable coin.1) 8887896 (publicSourceTable_length coin.1)

end Kriterion.ArgoMAC.ArithmeticSimulator
