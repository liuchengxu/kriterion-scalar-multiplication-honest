import Proof.Privacy.Simulator.Arithmetic.SelectedLabelsBits
import Proof.Privacy.Simulator.Arithmetic.WireCodec

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.SimulatorSampling GarbledCircuit.SimulatorProtocol

attribute [local irreducible] selectedLabelsFor selectedLabelsProgram

/-- The checked package keeps the fixed label program symbolic during type checking. -/
private noncomputable def selectedLabelsCodePackage : {program : List LinearInstruction // program = selectedLabelsProgram} :=
  Classical.choice ⟨⟨selectedLabelsProgram, rfl⟩⟩

/-- The compiled label code contains only fixed arithmetic, RAM reads, and bit writes. -/
noncomputable def selectedLabelsCode : List LinearInstruction := selectedLabelsCodePackage.val

theorem selectedLabelsCode_eq : selectedLabelsCode = selectedLabelsProgram := selectedLabelsCodePackage.property

theorem selectedLabelsCode_length : selectedLabelsCode.length = 200660 := by
  rw [selectedLabelsCode_eq, selectedLabelsProgram_length]

theorem selectedLabelsCode_fits : selectedLabelsCode.length < 2 ^ 256 := by
  rw [selectedLabelsCode_length]
  decide

/-- The standalone label machine charges every table entry. -/
noncomputable def selectedLabelsMachine : Machine := linearMachine selectedLabelsCode selectedLabelsCode_fits

/-- The label host block retains its exact source memory and instruction charge. -/
theorem selectedLabelsHost_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host selectedLabelsCode labels)
    (base : Memory) (fuel : Nat) :
    run host (200660 + fuel) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels 200660, executeLinear selectedLabelsCode base⟩).map
        (Option.map fun result => (result.1, result.2 + 200660)) := by
  simpa only [selectedLabelsCode_length] using linear_continue host selectedLabelsCode labels present base fuel

/-- The label machine returns all selected labels and preserves its source RAM. -/
theorem selectedLabelsMachine_run [BN254.FieldCertificate] (coin : OfflineCoin) (input : BN254.AffineInput)
    (base : Memory) (stored : WordsAt base.ram (base.registers 11) 0 (offlineSchedule.words coin))
    (coordinates : base.ram (base.registers 12) = BitVec.ofNat 256 input.x.val ∧
      base.ram (base.registers 12 + 1) = BitVec.ofNat 256 input.y.val) :
    (run selectedLabelsMachine (selectedLabelsCode.length + 1)
      ⟨⟨0, Nat.zero_lt_succ selectedLabelsMachine.size⟩, base⟩).map
      (Option.map fun result => (result.1.memory.bits 3, result.1.memory.ram, result.2)) =
      PMF.pure (some ((Lamport.selectedLabels (coin.2.1.encodeAffine input)).toList.flatMap
        (fun value => bits 128 value.toNat) ++ base.bits 3, base.ram, selectedLabelsCode.length + 1)) := by
  have emitted := selectedLabelsProgram_bits coin input base stored coordinates
  have saved := (selectedLabelsProgram_preserves base).1
  rw [← selectedLabelsCode_eq] at emitted saved
  unfold selectedLabelsMachine
  rw [linearMachine_run, PMF.pure_map]
  simp only [Option.map_some, emitted, Function.update_self, saved]

/-- The complete label charge includes its table, executed body, and final halt. -/
theorem selectedLabelsMachine_budget : selectedLabelsMachine.size + 1 + (selectedLabelsCode.length + 1) = 401322 := by
  change selectedLabelsCode.length + 1 + (selectedLabelsCode.length + 1) = _
  rw [selectedLabelsCode_length]

end Kriterion.ArgoMAC.ArithmeticSimulator
