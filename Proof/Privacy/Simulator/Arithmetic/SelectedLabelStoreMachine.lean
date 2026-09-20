import Proof.Privacy.Simulator.Arithmetic.SelectedLabelStore
import Proof.Privacy.Simulator.Arithmetic.SelectedLabelsMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.SimulatorSampling
attribute [local irreducible] selectedLabelStores selectedLabelStoreProgram Lamport.selectedLabels

/-- The checked package keeps the fixed store program symbolic. -/
private noncomputable def selectedLabelStoreCodePackage :
    {program : List LinearInstruction // program = selectedLabelStoreProgram} :=
  Classical.choice ⟨⟨selectedLabelStoreProgram, rfl⟩⟩

/-- The store code contains only fixed arithmetic and RAM instructions. -/
noncomputable def selectedLabelStoreCode : List LinearInstruction := selectedLabelStoreCodePackage.val

theorem selectedLabelStoreCode_eq : selectedLabelStoreCode = selectedLabelStoreProgram :=
  selectedLabelStoreCodePackage.property

theorem selectedLabelStoreCode_length : selectedLabelStoreCode.length = 7112 := by
  rw [selectedLabelStoreCode_eq, selectedLabelStoreProgram_length]

theorem selectedLabelStoreCode_fits : selectedLabelStoreCode.length < 2 ^ 256 := by
  rw [selectedLabelStoreCode_length]
  decide

/-- The standalone machine charges every store instruction. -/
noncomputable def selectedLabelStoreMachine : Machine := linearMachine selectedLabelStoreCode selectedLabelStoreCode_fits

/-- The host block returns after exactly 7112 instructions. -/
theorem selectedLabelStoreHost_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host selectedLabelStoreCode labels)
    (base : Memory) (fuel : Nat) :
    run host (7112 + fuel) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels 7112, executeLinear selectedLabelStoreCode base⟩).map
        (Option.map fun result => (result.1, result.2 + 7112)) := by
  simpa only [selectedLabelStoreCode_length] using
    linear_continue host selectedLabelStoreCode labels present base fuel

/-- The machine returns the exact typed label at each RAM index. -/
theorem selectedLabelStoreMachine_run [BN254.FieldCertificate] (coin : OfflineCoin)
    (input : BN254.AffineInput) (base : Memory)
    (stored : WordsAt base.ram (base.registers 11) 0 (offlineSchedule.words coin))
    (coordinates : base.ram (base.registers 12) = BitVec.ofNat 256 input.x.val ∧
      base.ram (base.registers 12 + 1) = BitVec.ofNat 256 input.y.val)
    (disjoint : SelectedStoreDisjoint base) (index : Fin 508) :
    (run selectedLabelStoreMachine (selectedLabelStoreCode.length + 1)
      ⟨⟨0, Nat.zero_lt_succ selectedLabelStoreMachine.size⟩, base⟩).map
      (Option.map fun result => (result.1.memory.ram
        (base.registers 14 + BitVec.ofNat 256 index.val), result.2)) =
      PMF.pure (some (((Lamport.selectedLabels (coin.2.1.encodeAffine input)).get index).setWidth 256,
        selectedLabelStoreCode.length + 1)) := by
  have source := selectedLabelStoreProgram_source coin input base stored coordinates disjoint index
  rw [← selectedLabelStoreCode_eq] at source
  unfold selectedLabelStoreMachine
  rw [linearMachine_run, PMF.pure_map]
  simp only [Option.map_some, source]

/-- The total store charge includes its table, body, and final halt. -/
theorem selectedLabelStoreMachine_budget :
    selectedLabelStoreMachine.size + 1 + (selectedLabelStoreCode.length + 1) = 14226 := by
  change selectedLabelStoreCode.length + 1 + (selectedLabelStoreCode.length + 1) = _
  rw [selectedLabelStoreCode_length]

end Kriterion.ArgoMAC.ArithmeticSimulator
