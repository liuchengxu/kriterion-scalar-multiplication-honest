import Proof.Privacy.Simulator.Arithmetic.SelectedLabelsMachine
import Proof.Privacy.Simulator.Arithmetic.CanonicalPublic

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.SimulatorSampling GarbledCircuit.SimulatorProtocol
attribute [local irreducible] selectedLabelsFor selectedLabelsProgram words run Lamport.selectedLabels

/-- The host code emits the exact selected signature before it returns. -/
theorem selectedLabelsCode_bits [BN254.FieldCertificate] (coin : OfflineCoin) (input : BN254.AffineInput)
    (base : Memory) (stored : WordsAt base.ram (base.registers 11) 0 (offlineSchedule.words coin))
    (coordinates : base.ram (base.registers 12) = BitVec.ofNat 256 input.x.val ∧
      base.ram (base.registers 12 + 1) = BitVec.ofNat 256 input.y.val) :
    (executeLinear selectedLabelsCode base).bits = Function.update base.bits 3
      ((Lamport.selectedLabels (coin.2.1.encodeAffine input)).toList.flatMap
        (fun value => bits 128 value.toNat) ++ base.bits 3) := by
  rw [selectedLabelsCode_eq]
  exact selectedLabelsProgram_bits coin input base stored coordinates

/-- The protocol parser accepts exactly the original 508 selected labels. -/
theorem selectedLabelsMachine_protocol [BN254.FieldCertificate] (coin : OfflineCoin) (input : BN254.AffineInput)
    (base : Memory) (stored : WordsAt base.ram (base.registers 11) 0 (offlineSchedule.words coin))
    (coordinates : base.ram (base.registers 12) = BitVec.ofNat 256 input.x.val ∧
      base.ram (base.registers 12 + 1) = BitVec.ofNat 256 input.y.val) (empty : base.bits 3 = []) :
    (run selectedLabelsMachine (selectedLabelsCode.length + 1)
      ⟨⟨0, Nat.zero_lt_succ selectedLabelsMachine.size⟩, base⟩).map
      (fun result => result.bind fun result => words 128 508 (result.1.memory.bits 3)) =
      PMF.pure (some (Lamport.selectedLabels (coin.2.1.encodeAffine input))) := by
  apply parse_mapped_output
    (run selectedLabelsMachine (selectedLabelsCode.length + 1)
      ⟨⟨0, Nat.zero_lt_succ selectedLabelsMachine.size⟩, base⟩)
    (fun result : Configuration (selectedLabelsMachine.size + 1) × Nat => (result.1.memory.bits 3, result.1.memory.ram, result.2))
    (fun result : List Bool × (Word → Word) × Nat => words 128 508 result.1)
    _ _ (selectedLabelsMachine_run coin input base stored coordinates)
  rw [empty, List.append_nil]
  exact words_encoded 128 508 (Lamport.selectedLabels (coin.2.1.encodeAffine input))

end Kriterion.ArgoMAC.ArithmeticSimulator
