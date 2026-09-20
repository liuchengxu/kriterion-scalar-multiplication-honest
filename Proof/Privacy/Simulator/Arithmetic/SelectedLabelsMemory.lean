import Proof.Privacy.Simulator.Arithmetic.SelectedLabelSegment

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The emitter reverses execution order to preserve signature order on its output stack. -/
def selectedLabelsFor (indices : List (Fin 508)) : List LinearInstruction :=
  indices.reverse.flatMap selectedLabelSegment

/-- A nonempty source emits its tail before its first label. -/
theorem selectedLabelsFor_cons (index : Fin 508) (indices : List (Fin 508)) :
    selectedLabelsFor (index :: indices) = selectedLabelsFor indices ++ selectedLabelSegment index := by
  simp [selectedLabelsFor, List.reverse_cons]

/-- The label emitter preserves its source RAM and all caller registers. -/
theorem selectedLabelsFor_preserves (indices : List (Fin 508)) (base : Memory) :
    (executeLinear (selectedLabelsFor indices) base).ram = base.ram ∧
    ∀ register : Register, 11 ≤ register.val →
      (executeLinear (selectedLabelsFor indices) base).registers register = base.registers register := by
  induction indices with
  | nil => simp [selectedLabelsFor, executeLinear]
  | cons index indices ih =>
      rw [selectedLabelsFor_cons, executeLinear_append]
      refine ⟨(selectedLabelSegment_ram index _).trans ih.1, ?_⟩
      intro register caller
      exact (selectedLabelSegment_caller index _ register caller).trans (ih.2 register caller)

/-- The label emitter retains the exact selected word for every label position. -/
theorem selectedLabelsFor_source (indices : List (Fin 508)) (base : Memory) (index : Fin 508) :
    selectedLabelWord index (executeLinear (selectedLabelsFor indices) base) = selectedLabelWord index base := by
  have saved := selectedLabelsFor_preserves indices base
  simp only [selectedLabelWord, selectedBitWord, saved.1, saved.2 11 (by decide), saved.2 12 (by decide)]

/-- The label emitter returns its exact canonical bit sequence. -/
theorem selectedLabelsFor_bits (indices : List (Fin 508)) (base : Memory) :
    (executeLinear (selectedLabelsFor indices) base).bits = Function.update base.bits 3
      (indices.flatMap (fun index => GarbledCircuit.SimulatorProtocol.bits 128 (selectedLabelWord index base).toNat) ++ base.bits 3) := by
  induction indices with
  | nil => simp [selectedLabelsFor, executeLinear, Function.update_eq_self]
  | cons index indices ih =>
      rw [selectedLabelsFor_cons, executeLinear_append, selectedLabelSegment_bits, selectedLabelsFor_source, ih]
      simp [List.append_assoc]

/-- The emitter charges exactly 395 instructions per label. -/
theorem selectedLabelsFor_length (indices : List (Fin 508)) : (selectedLabelsFor indices).length = 395 * indices.length := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      rw [selectedLabelsFor_cons, List.length_append, selectedLabelSegment_length, ih]
      simp [Nat.mul_add, Nat.add_comm]

/-- The complete signature body contains exactly 200660 fixed instructions. -/
theorem selectedLabelsProgram_length : selectedLabelsProgram.length = 200660 := by
  change (selectedLabelsFor (List.finRange 508)).length = _
  rw [selectedLabelsFor_length, List.length_finRange]

/-- The complete signature program uses the finite label order. -/
theorem selectedLabelsProgram_eq : selectedLabelsProgram = selectedLabelsFor (List.finRange 508) := rfl

attribute [local irreducible] selectedLabelsFor selectedLabelsProgram

/-- The complete signature emitter retains all source data. -/
theorem selectedLabelsProgram_preserves (base : Memory) :
    (executeLinear selectedLabelsProgram base).ram = base.ram ∧
    ∀ register : Register, 11 ≤ register.val →
      (executeLinear selectedLabelsProgram base).registers register = base.registers register := by
  rw [selectedLabelsProgram_eq]
  exact selectedLabelsFor_preserves (List.finRange 508) base

end Kriterion.ArgoMAC.ArithmeticSimulator
