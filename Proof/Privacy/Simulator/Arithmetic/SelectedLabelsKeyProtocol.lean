import Proof.Privacy.Simulator.Arithmetic.SelectedLabelKeySource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.SimulatorSampling GarbledCircuit.SimulatorProtocol
attribute [local irreducible] selectedLabelsFor selectedLabelsProgram words run Lamport.selectedLabels

/-- The complete emitter produces exactly the original 508 selected labels. -/
theorem selectedLabelsProgram_keyBits [BN254.FieldCertificate] (key : InputMacKey) (input : BN254.AffineInput)
    (base : Memory) (stored : WordsAt base.ram (base.registers 11) 1 (inputKeySchedule.words key))
    (coordinates : base.ram (base.registers 12) = BitVec.ofNat 256 input.x.val ∧
      base.ram (base.registers 12 + 1) = BitVec.ofNat 256 input.y.val) :
    (executeLinear selectedLabelsProgram base).bits = Function.update base.bits 3
      ((Lamport.selectedLabels (key.encodeAffine input)).toList.flatMap
        (fun value => GarbledCircuit.SimulatorProtocol.bits 128 value.toNat) ++ base.bits 3) := by
  rw [selectedLabelsProgram_eq, selectedLabelsFor_bits, vector_toList_finRange, List.flatMap_map]
  apply congrArg (Function.update base.bits 3)
  apply congrArg (fun words => words ++ base.bits 3)
  apply congrArg (fun encode => (List.finRange 508).flatMap encode)
  funext index
  rw [selectedLabelWord_keySource key input base stored coordinates index, BitVec.toNat_setWidth_of_le (by decide)]

/-- The label machine returns all selected labels and preserves its source RAM. -/
theorem selectedLabelsMachine_keyRun [BN254.FieldCertificate] (key : InputMacKey) (input : BN254.AffineInput)
    (base : Memory) (stored : WordsAt base.ram (base.registers 11) 1 (inputKeySchedule.words key))
    (coordinates : base.ram (base.registers 12) = BitVec.ofNat 256 input.x.val ∧
      base.ram (base.registers 12 + 1) = BitVec.ofNat 256 input.y.val) :
    (run selectedLabelsMachine (selectedLabelsCode.length + 1)
      ⟨⟨0, Nat.zero_lt_succ selectedLabelsMachine.size⟩, base⟩).map
      (Option.map fun result => (result.1.memory.bits 3, result.1.memory.ram, result.2)) =
      PMF.pure (some ((Lamport.selectedLabels (key.encodeAffine input)).toList.flatMap
        (fun value => bits 128 value.toNat) ++ base.bits 3, base.ram, selectedLabelsCode.length + 1)) := by
  have emitted := selectedLabelsProgram_keyBits key input base stored coordinates
  have saved := (selectedLabelsProgram_preserves base).1
  rw [← selectedLabelsCode_eq] at emitted saved
  unfold selectedLabelsMachine
  rw [linearMachine_run, PMF.pure_map]
  simp only [Option.map_some, emitted, Function.update_self, saved]

/-- The host code emits the exact selected signature before it returns. -/
theorem selectedLabelsCode_keyBits [BN254.FieldCertificate] (key : InputMacKey) (input : BN254.AffineInput)
    (base : Memory) (stored : WordsAt base.ram (base.registers 11) 1 (inputKeySchedule.words key))
    (coordinates : base.ram (base.registers 12) = BitVec.ofNat 256 input.x.val ∧
      base.ram (base.registers 12 + 1) = BitVec.ofNat 256 input.y.val) :
    (executeLinear selectedLabelsCode base).bits = Function.update base.bits 3
      ((Lamport.selectedLabels (key.encodeAffine input)).toList.flatMap
        (fun value => bits 128 value.toNat) ++ base.bits 3) := by
  rw [selectedLabelsCode_eq]
  exact selectedLabelsProgram_keyBits key input base stored coordinates

/-- The protocol parser accepts exactly the original 508 selected labels. -/
theorem selectedLabelsMachine_keyProtocol [BN254.FieldCertificate] (key : InputMacKey) (input : BN254.AffineInput)
    (base : Memory) (stored : WordsAt base.ram (base.registers 11) 1 (inputKeySchedule.words key))
    (coordinates : base.ram (base.registers 12) = BitVec.ofNat 256 input.x.val ∧
      base.ram (base.registers 12 + 1) = BitVec.ofNat 256 input.y.val) (empty : base.bits 3 = []) :
    (run selectedLabelsMachine (selectedLabelsCode.length + 1)
      ⟨⟨0, Nat.zero_lt_succ selectedLabelsMachine.size⟩, base⟩).map
      (fun result => result.bind fun result => words 128 508 (result.1.memory.bits 3)) =
      PMF.pure (some (Lamport.selectedLabels (key.encodeAffine input))) := by
  apply parse_mapped_output
    (run selectedLabelsMachine (selectedLabelsCode.length + 1)
      ⟨⟨0, Nat.zero_lt_succ selectedLabelsMachine.size⟩, base⟩)
    (fun result : Configuration (selectedLabelsMachine.size + 1) × Nat => (result.1.memory.bits 3, result.1.memory.ram, result.2))
    (fun result : List Bool × (Word → Word) × Nat => words 128 508 result.1)
    _ _ (selectedLabelsMachine_keyRun key input base stored coordinates)
  rw [empty, List.append_nil]
  exact words_encoded 128 508 (Lamport.selectedLabels (key.encodeAffine input))

end Kriterion.ArgoMAC.ArithmeticSimulator
