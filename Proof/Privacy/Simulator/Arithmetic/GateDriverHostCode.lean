import Proof.Privacy.Simulator.Arithmetic.GateDriverCode

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host keeps separate normal and cutoff returns for one complete gate. -/
def ContainsGateDriver (host : Machine) (attempts : Nat) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 1036, pc ≠ 1034 → pc ≠ 1035 → host.code[(labels pc).val] =
    relocate labels ((gateDriver attempts gate).code[pc.val]'pc.isLt)

/-- Every fixed gate block retains its caller labels. -/
theorem gateDriverBlock_linear (host : Machine) (attempts : Nat) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsGateDriver host attempts gate labels)
    (program : List LinearInstruction) (sourceLabels : Nat → Fin 1036)
    (source : ContainsLinear (gateDriver attempts gate) program sourceLabels)
    (inside : ∀ index, index < program.length → sourceLabels index ≠ 1034 ∧ sourceLabels index ≠ 1035) :
    ContainsLinear host program (labels ∘ sourceLabels) := by
  intro index valid
  exact (present (sourceLabels index) (inside index valid).1 (inside index valid).2).trans
    ((congrArg (relocate labels) (source index valid)).trans (LinearInstruction.relocate_emit labels _ _))

theorem gateDriverBlock_load (host : Machine) (attempts : Nat) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsGateDriver host attempts gate labels) :
    ContainsLinear host (gateDirectiveLoad gate.selected gate.target gate.quotient gate.table) (labels ∘ gateDriverLoadLabels) := by
  apply gateDriverBlock_linear host attempts gate labels present (gateDirectiveLoad gate.selected gate.target gate.quotient gate.table) gateDriverLoadLabels (gateDriver_load attempts gate)
  intro index valid
  have bound : index < 21 := valid
  have value : (gateDriverLoadLabels index).val = 0 + index := by
    change (gateDriverLinearLabels 0 21 (by decide) 21 index).val = _
    simp only [gateDriverLinearLabels, dif_pos bound]
  constructor <;> intro equal <;> have vals := congrArg Fin.val equal <;> rw [value] at vals <;> change 0 + index = _ at vals <;> omega

theorem gateDriverBlock_save (host : Machine) (attempts : Nat) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsGateDriver host attempts gate labels) :
    ContainsLinear host gateDirectiveSave (labels ∘ gateDriverSaveLabels) := by
  apply gateDriverBlock_linear host attempts gate labels present gateDirectiveSave gateDriverSaveLabels (gateDriver_save attempts gate)
  intro index valid
  have bound : index < 20 := valid
  have value : (gateDriverSaveLabels index).val = 60 + index := by
    change (gateDriverLinearLabels 60 20 (by decide) 80 index).val = _
    simp only [gateDriverLinearLabels, dif_pos bound]
  constructor <;> intro equal <;> have vals := congrArg Fin.val equal <;> rw [value] at vals <;> change 60 + index = _ at vals <;> omega

theorem gateDriverBlock_load0 (host : Machine) (attempts : Nat) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsGateDriver host attempts gate labels) :
    ContainsLinear host (gateSlotLoad (gate.oracle 0) 0) (labels ∘ (gateDriverSlotLoadLabels 0)) := by
  apply gateDriverBlock_linear host attempts gate labels present (gateSlotLoad (gate.oracle 0) 0) (gateDriverSlotLoadLabels 0) (gateDriver_load0 attempts gate)
  intro index valid
  have bound : index < 8 := valid
  have value : ((gateDriverSlotLoadLabels 0) index).val = 80 + index := by
    change (gateDriverLinearLabels 80 8 (by decide) 88 index).val = _
    simp only [gateDriverLinearLabels, dif_pos bound]
  constructor <;> intro equal <;> have vals := congrArg Fin.val equal <;> rw [value] at vals <;> change 80 + index = _ at vals <;> omega

theorem gateDriverBlock_load1 (host : Machine) (attempts : Nat) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsGateDriver host attempts gate labels) :
    ContainsLinear host (gateSlotLoad (gate.oracle 1) 1) (labels ∘ (gateDriverSlotLoadLabels 1)) := by
  apply gateDriverBlock_linear host attempts gate labels present (gateSlotLoad (gate.oracle 1) 1) (gateDriverSlotLoadLabels 1) (gateDriver_load1 attempts gate)
  intro index valid
  have bound : index < 8 := valid
  have value : ((gateDriverSlotLoadLabels 1) index).val = 393 + index := by
    change (gateDriverLinearLabels 393 8 (by decide) 401 index).val = _
    simp only [gateDriverLinearLabels, dif_pos bound]
  constructor <;> intro equal <;> have vals := congrArg Fin.val equal <;> rw [value] at vals <;> change 393 + index = _ at vals <;> omega

theorem gateDriverBlock_test (host : Machine) (attempts : Nat) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsGateDriver host attempts gate labels) :
    ContainsLinear host gateDriverTest (labels ∘ gateDriverTestLabels) := by
  apply gateDriverBlock_linear host attempts gate labels present gateDriverTest gateDriverTestLabels (gateDriver_test attempts gate)
  intro index valid
  have bound : index < 4 := valid
  have value : (gateDriverTestLabels index).val = 706 + index := by
    change (gateDriverLinearLabels 706 4 (by decide) 710 index).val = _
    simp only [gateDriverLinearLabels, dif_pos bound]
  constructor <;> intro equal <;> have vals := congrArg Fin.val equal <;> rw [value] at vals <;> change 706 + index = _ at vals <;> omega

theorem gateDriverBlock_load2 (host : Machine) (attempts : Nat) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsGateDriver host attempts gate labels) :
    ContainsLinear host (gateSlotLoad (gate.oracle 2) 2) (labels ∘ (gateDriverSlotLoadLabels 2)) := by
  apply gateDriverBlock_linear host attempts gate labels present (gateSlotLoad (gate.oracle 2) 2) (gateDriverSlotLoadLabels 2) (gateDriver_load2 attempts gate)
  intro index valid
  have bound : index < 8 := valid
  have value : ((gateDriverSlotLoadLabels 2) index).val = 711 + index := by
    change (gateDriverLinearLabels 711 8 (by decide) 719 index).val = _
    simp only [gateDriverLinearLabels, dif_pos bound]
  constructor <;> intro equal <;> have vals := congrArg Fin.val equal <;> rw [value] at vals <;> change 711 + index = _ at vals <;> omega

theorem gateDriverBlock_restore (host : Machine) (attempts : Nat) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsGateDriver host attempts gate labels) :
    ContainsLinear host gateDirectiveRestore (labels ∘ gateDriverRestoreLabels) := by
  apply gateDriverBlock_linear host attempts gate labels present gateDirectiveRestore gateDriverRestoreLabels (gateDriver_restore attempts gate)
  intro index valid
  have bound : index < 10 := valid
  have value : (gateDriverRestoreLabels index).val = 1024 + index := by
    change (gateDriverLinearLabels 1024 10 (by decide) 1034 index).val = _
    simp only [gateDriverLinearLabels, dif_pos bound]
  constructor <;> intro equal <;> have vals := congrArg Fin.val equal <;> rw [value] at vals <;> change 1024 + index = _ at vals <;> omega

theorem gateDriverBlock_blocks (host : Machine) (attempts : Nat) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsGateDriver host attempts gate labels) :
    ContainsGateBlocks host gate.tweak (labels ∘ gateDriverBlocksLabels) := by
  intro pc active
  have notExit : pc ≠ 38 := by intro equal; have vals := congrArg Fin.val equal; omega
  have value : (gateDriverBlocksLabels pc).val = 21 + pc.val := by simp [gateDriverBlocksLabels, notExit]
  have first : gateDriverBlocksLabels pc ≠ 1034 := by
    intro equal; have vals := congrArg Fin.val equal; rw [value] at vals; omega
  have second : gateDriverBlocksLabels pc ≠ 1035 := by
    intro equal; have vals := congrArg Fin.val equal; rw [value] at vals; omega
  exact (present _ first second).trans ((congrArg (relocate labels) (gateDriver_blocks attempts gate pc active)).trans
    (relocate_comp gateDriverBlocksLabels labels _))

theorem gateDriverBlock_slot0 (host : Machine) (attempts : Nat) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsGateDriver host attempts gate labels) :
    ContainsCheckedSlot host attempts (labels ∘ gateDriverSlotLabels 0) := by
  intro pc normal cutoff
  have value : (gateDriverSlotLabels 0 pc).val = 88 + pc.val := by
    simp only [gateDriverSlotLabels, if_neg cutoff, if_neg normal, show (0 : Fin 3).val = 0 from rfl]
  have first : gateDriverSlotLabels 0 pc ≠ 1034 := by
    intro equal; have vals := congrArg Fin.val equal; rw [value] at vals; have bound := pc.isLt; omega
  have second : gateDriverSlotLabels 0 pc ≠ 1035 := by
    intro equal; have vals := congrArg Fin.val equal; rw [value] at vals; have bound := pc.isLt; omega
  exact (present _ first second).trans ((congrArg (relocate labels) (gateDriver_slot0 attempts gate pc normal cutoff)).trans
    (relocate_comp (gateDriverSlotLabels 0) labels _))

theorem gateDriverBlock_slot1 (host : Machine) (attempts : Nat) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsGateDriver host attempts gate labels) :
    ContainsCheckedSlot host attempts (labels ∘ gateDriverSlotLabels 1) := by
  intro pc normal cutoff
  have value : (gateDriverSlotLabels 1 pc).val = 401 + pc.val := by
    simp only [gateDriverSlotLabels, if_neg cutoff, if_neg normal, show (1 : Fin 3).val = 1 from rfl]
  have first : gateDriverSlotLabels 1 pc ≠ 1034 := by
    intro equal; have vals := congrArg Fin.val equal; rw [value] at vals; have bound := pc.isLt; omega
  have second : gateDriverSlotLabels 1 pc ≠ 1035 := by
    intro equal; have vals := congrArg Fin.val equal; rw [value] at vals; have bound := pc.isLt; omega
  exact (present _ first second).trans ((congrArg (relocate labels) (gateDriver_slot1 attempts gate pc normal cutoff)).trans
    (relocate_comp (gateDriverSlotLabels 1) labels _))

theorem gateDriverBlock_slot2 (host : Machine) (attempts : Nat) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsGateDriver host attempts gate labels) :
    ContainsCheckedSlot host attempts (labels ∘ gateDriverSlotLabels 2) := by
  intro pc normal cutoff
  have value : (gateDriverSlotLabels 2 pc).val = 719 + pc.val := by
    simp only [gateDriverSlotLabels, if_neg cutoff, if_neg normal, show (2 : Fin 3).val = 2 from rfl]
  have first : gateDriverSlotLabels 2 pc ≠ 1034 := by
    intro equal; have vals := congrArg Fin.val equal; rw [value] at vals; have bound := pc.isLt; omega
  have second : gateDriverSlotLabels 2 pc ≠ 1035 := by
    intro equal; have vals := congrArg Fin.val equal; rw [value] at vals; have bound := pc.isLt; omega
  exact (present _ first second).trans ((congrArg (relocate labels) (gateDriver_slot2 attempts gate pc normal cutoff)).trans
    (relocate_comp (gateDriverSlotLabels 2) labels _))

end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The private arithmetic keeps each instruction outside the oracle capsules. -/
theorem lazyGateInstruction_private (gate : GateCode) (pc : Fin 1036)
    (outside : pc.val ∉ [88, 89, 90, 401, 402, 403, 719, 720, 721]) :
    lazyGateInstruction gate pc = .compute ((gateDriver 256 gate).code[pc.val]) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  simp_all [lazyGateInstruction]

/-- The host contains the complete fixed-oracle gate before its normal return. -/
def ContainsLazyGateDriver (host : Simulator) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 1036, pc.val < 1034 → host.code[(labels pc).val] =
    relocateSimulator labels (lazyGateInstruction gate pc)

/-- Each unchanged arithmetic block keeps its source memory effect. -/
theorem lazyGateDriverBlock_linear (host : Simulator) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsLazyGateDriver host gate labels)
    (program : List LinearInstruction) (sourceLabels : Nat → Fin 1036)
    (source : ContainsLinear (gateDriver 256 gate) program sourceLabels)
    (inside : ∀ index, index < program.length → (sourceLabels index).val < 1034 ∧
      (sourceLabels index).val ∉ [88, 89, 90, 401, 402, 403, 719, 720, 721]) :
    ContainsLinear host.arithmetic program (labels ∘ sourceLabels) := by
  intro index valid
  have code := present (sourceLabels index) (inside index valid).1
  rw [lazyGateInstruction_private gate (sourceLabels index) (inside index valid).2] at code
  rw [source index valid] at code
  simp only [relocateSimulator, LinearInstruction.relocate_emit] at code
  simp [Simulator.arithmetic, Function.comp_def, code]
  exact LinearInstruction.relocate_emit labels _ _

end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

theorem lazyGateDriverBlock_load (host : Simulator) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsLazyGateDriver host gate labels) :
    ContainsLinear host.arithmetic (gateDirectiveLoad gate.selected gate.target gate.quotient gate.table) (labels ∘ gateDriverLoadLabels) := by
  apply lazyGateDriverBlock_linear host gate labels present (gateDirectiveLoad gate.selected gate.target gate.quotient gate.table) gateDriverLoadLabels (gateDriver_load 256 gate)
  intro index valid
  have bound : index < 21 := valid
  simp only [gateDriverLoadLabels, gateDriverSaveLabels, gateDriverSlotLoadLabels,
    gateDriverTestLabels, gateDriverRestoreLabels, gateDriverLinearLabels, dif_pos bound,
    show (0 : Fin 3).val = 0 from rfl, show (1 : Fin 3).val = 1 from rfl,
    List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem lazyGateDriverBlock_save (host : Simulator) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsLazyGateDriver host gate labels) :
    ContainsLinear host.arithmetic gateDirectiveSave (labels ∘ gateDriverSaveLabels) := by
  apply lazyGateDriverBlock_linear host gate labels present gateDirectiveSave gateDriverSaveLabels (gateDriver_save 256 gate)
  intro index valid
  have bound : index < 20 := valid
  simp only [gateDriverLoadLabels, gateDriverSaveLabels, gateDriverSlotLoadLabels,
    gateDriverTestLabels, gateDriverRestoreLabels, gateDriverLinearLabels, dif_pos bound,
    show (0 : Fin 3).val = 0 from rfl, show (1 : Fin 3).val = 1 from rfl,
    List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem lazyGateDriverBlock_load0 (host : Simulator) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsLazyGateDriver host gate labels) :
    ContainsLinear host.arithmetic (gateSlotLoad (gate.oracle 0) 0) (labels ∘ (gateDriverSlotLoadLabels 0)) := by
  apply lazyGateDriverBlock_linear host gate labels present (gateSlotLoad (gate.oracle 0) 0) (gateDriverSlotLoadLabels 0) (gateDriver_load0 256 gate)
  intro index valid
  have bound : index < 8 := valid
  simp only [gateDriverLoadLabels, gateDriverSaveLabels, gateDriverSlotLoadLabels,
    gateDriverTestLabels, gateDriverRestoreLabels, gateDriverLinearLabels, dif_pos bound,
    show (0 : Fin 3).val = 0 from rfl, show (1 : Fin 3).val = 1 from rfl,
    List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem lazyGateDriverBlock_load1 (host : Simulator) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsLazyGateDriver host gate labels) :
    ContainsLinear host.arithmetic (gateSlotLoad (gate.oracle 1) 1) (labels ∘ (gateDriverSlotLoadLabels 1)) := by
  apply lazyGateDriverBlock_linear host gate labels present (gateSlotLoad (gate.oracle 1) 1) (gateDriverSlotLoadLabels 1) (gateDriver_load1 256 gate)
  intro index valid
  have bound : index < 8 := valid
  simp only [gateDriverLoadLabels, gateDriverSaveLabels, gateDriverSlotLoadLabels,
    gateDriverTestLabels, gateDriverRestoreLabels, gateDriverLinearLabels, dif_pos bound,
    show (0 : Fin 3).val = 0 from rfl, show (1 : Fin 3).val = 1 from rfl,
    List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem lazyGateDriverBlock_test (host : Simulator) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsLazyGateDriver host gate labels) :
    ContainsLinear host.arithmetic gateDriverTest (labels ∘ gateDriverTestLabels) := by
  apply lazyGateDriverBlock_linear host gate labels present gateDriverTest gateDriverTestLabels (gateDriver_test 256 gate)
  intro index valid
  have bound : index < 4 := valid
  simp only [gateDriverLoadLabels, gateDriverSaveLabels, gateDriverSlotLoadLabels,
    gateDriverTestLabels, gateDriverRestoreLabels, gateDriverLinearLabels, dif_pos bound,
    show (0 : Fin 3).val = 0 from rfl, show (1 : Fin 3).val = 1 from rfl,
    List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem lazyGateDriverBlock_load2 (host : Simulator) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsLazyGateDriver host gate labels) :
    ContainsLinear host.arithmetic (gateSlotLoad (gate.oracle 2) 2) (labels ∘ (gateDriverSlotLoadLabels 2)) := by
  apply lazyGateDriverBlock_linear host gate labels present (gateSlotLoad (gate.oracle 2) 2) (gateDriverSlotLoadLabels 2) (gateDriver_load2 256 gate)
  intro index valid
  have bound : index < 8 := valid
  simp only [gateDriverLoadLabels, gateDriverSaveLabels, gateDriverSlotLoadLabels,
    gateDriverTestLabels, gateDriverRestoreLabels, gateDriverLinearLabels, dif_pos bound,
    show (0 : Fin 3).val = 0 from rfl, show (1 : Fin 3).val = 1 from rfl,
    List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem lazyGateDriverBlock_restore (host : Simulator) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsLazyGateDriver host gate labels) :
    ContainsLinear host.arithmetic gateDirectiveRestore (labels ∘ gateDriverRestoreLabels) := by
  apply lazyGateDriverBlock_linear host gate labels present gateDirectiveRestore gateDriverRestoreLabels (gateDriver_restore 256 gate)
  intro index valid
  have bound : index < 10 := valid
  simp only [gateDriverLoadLabels, gateDriverSaveLabels, gateDriverSlotLoadLabels,
    gateDriverTestLabels, gateDriverRestoreLabels, gateDriverLinearLabels, dif_pos bound,
    show (0 : Fin 3).val = 0 from rfl, show (1 : Fin 3).val = 1 from rfl,
    List.mem_cons, List.not_mem_nil, or_false]
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The fixed-oracle host retains both private gate arithmetic branches. -/
theorem lazyGateDriverBlock_blocks (host : Simulator) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsLazyGateDriver host gate labels) :
    ContainsGateBlocks host.arithmetic gate.tweak (labels ∘ gateDriverBlocksLabels) := by
  intro pc active
  have notExit : pc ≠ 38 := by intro same; have := congrArg Fin.val same; omega
  have value : (gateDriverBlocksLabels pc).val = 21 + pc.val := by
    simp [gateDriverBlocksLabels, notExit]
  have bound : (gateDriverBlocksLabels pc).val < 1034 := by rw [value]; omega
  have outside : (gateDriverBlocksLabels pc).val ∉ [88, 89, 90, 401, 402, 403, 719, 720, 721] := by
    rw [value]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have code := present (gateDriverBlocksLabels pc) bound
  rw [lazyGateInstruction_private gate _ outside, gateDriver_blocks 256 gate pc active] at code
  simp only [relocateSimulator, relocate_comp] at code
  simp [Simulator.arithmetic, Function.comp_def, code]
  exact relocate_comp gateDriverBlocksLabels labels _

end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The three-instruction capsule retains the existing slot return. -/
def lazyGateProgramLabels (slot : Fin 3) (index : Nat) : Fin 1036 :=
  gateDriverSlotLabels slot (if inside : index < 3 then ⟨index, by omega⟩ else 300)

/-- Every embedded slot contains the same load and fresh-program sequence. -/
theorem lazyGateDriverBlock_program (host : Simulator) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsLazyGateDriver host gate labels)
    (slot : Fin 3) :
    host.code[(labels (lazyGateProgramLabels slot 0)).val] =
        .compute (.constant 0 14 (labels (lazyGateProgramLabels slot 1))) ∧
    host.code[(labels (lazyGateProgramLabels slot 1)).val] =
        .compute (.load 1 0 (labels (lazyGateProgramLabels slot 2))) ∧
    host.code[(labels (lazyGateProgramLabels slot 2)).val] =
        .program 0 9 8 1 2 (labels (lazyGateProgramLabels slot 3)) := by
  have first := present (lazyGateProgramLabels slot 0) (by
    fin_cases slot <;> simp [lazyGateProgramLabels, gateDriverSlotLabels])
  have second := present (lazyGateProgramLabels slot 1) (by
    fin_cases slot <;> simp [lazyGateProgramLabels, gateDriverSlotLabels])
  have third := present (lazyGateProgramLabels slot 2) (by
    fin_cases slot <;> simp [lazyGateProgramLabels, gateDriverSlotLabels])
  fin_cases slot <;>
    simp [lazyGateProgramLabels, gateDriverSlotLabels, lazyGateInstruction,
      relocateSimulator, relocate] at first second third ⊢ <;> exact ⟨first, second, third⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
