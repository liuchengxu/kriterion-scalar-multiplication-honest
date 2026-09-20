import Construction.Simulator.WireSegments
import Proof.Privacy.Simulator.Arithmetic.ByteOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
set_option maxRecDepth 4096

/-- The source wire reads one payload word or emits a zero pad. -/
def WireSegment.wire (ram : Word → Word) (base : Word) : WireSegment → List Bool
  | .stored offset => bits coordinateBitCount (ram (base + offset)).toNat
  | .zero width => bits width.val 0

/-- One segment retains RAM and the source address. -/
theorem wireSegment_preserves (segment : WireSegment) (memory : Memory) :
    let result := executeLinear segment.program memory
    result.ram = memory.ram ∧ result.registers 11 = memory.registers 11 := by
  cases segment <;>
    simp only [WireSegment.program, executeLinear, List.foldl_append, List.foldl_cons, List.foldl_nil]
  all_goals change (executeLinear (wordOutput _) _).ram = _ ∧
    (executeLinear (wordOutput _) _).registers 11 = _
  all_goals rw [wordOutput_ram, wordOutput_saved _ _ 11 (by decide) (by decide)]
  all_goals simp [LinearInstruction.execute, Arithmetic.eval]

/-- One segment prepends its exact canonical wire. -/
theorem wireSegment_bits (segment : WireSegment) (memory : Memory) :
    (executeLinear segment.program memory).bits =
      Function.update memory.bits 3 (segment.wire memory.ram (memory.registers 11) ++ memory.bits 3) := by
  cases segment with
  | stored offset =>
      simp only [WireSegment.program, executeLinear, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (executeLinear (wordOutput coordinateBitCount) _).bits = _
      rw [wordOutput_bits _ _ (by decide), wordOutput_protocol]
      simp [WireSegment.wire, LinearInstruction.execute, Arithmetic.eval]
  | zero width =>
      simp only [WireSegment.program, executeLinear, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (executeLinear (wordOutput width) _).bits = _
      rw [wordOutput_bits _ _ (by have := width.isLt; omega), wordOutput_protocol]
      simp [WireSegment.wire, LinearInstruction.execute]

/-- Every segment costs at most 771 fixed instructions. -/
theorem wireSegment_length (segment : WireSegment) : segment.program.length ≤ 771 := by
  cases segment with
  | stored offset =>
      simp only [WireSegment.program, List.length_append, List.length_cons, List.length_nil,
        wordOutput_length, coordinateBitCount]
      decide
  | zero width =>
      simp only [WireSegment.program, List.length_append, List.length_cons, List.length_nil,
        wordOutput_length]
      have := width.isLt
      omega

/-- The emitter retains its source RAM and base address. -/
theorem wireSegments_preserves (segments : List WireSegment) (memory : Memory) :
    let result := executeLinear (wireSegmentsProgram segments) memory
    result.ram = memory.ram ∧ result.registers 11 = memory.registers 11 := by
  induction segments generalizing memory with
  | nil => simp [wireSegmentsProgram, executeLinear]
  | cons head tail ih =>
      have first := ih memory
      have second := wireSegment_preserves head (executeLinear (wireSegmentsProgram tail) memory)
      simpa only [wireSegmentsProgram, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, executeLinear, List.foldl_append] using
        And.intro (second.1.trans first.1) (second.2.trans first.2)

/-- The emitter prepends all source segments in their specified order. -/
theorem wireSegments_bits (segments : List WireSegment) (memory : Memory) :
    (executeLinear (wireSegmentsProgram segments) memory).bits =
      Function.update memory.bits 3
        (segments.flatMap (WireSegment.wire memory.ram (memory.registers 11)) ++ memory.bits 3) := by
  induction segments generalizing memory with
  | nil => simp [wireSegmentsProgram, executeLinear, Function.update_eq_self]
  | cons head tail ih =>
      have saved := wireSegments_preserves tail memory
      simp only [wireSegmentsProgram, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, executeLinear, List.foldl_append]
      change (executeLinear head.program (executeLinear (wireSegmentsProgram tail) memory)).bits = _
      rw [wireSegment_bits, saved.1, saved.2, ih]
      simp [List.append_assoc]

/-- The fixed instruction count is linear in the number of source segments. -/
theorem wireSegments_length (segments : List WireSegment) :
    (wireSegmentsProgram segments).length ≤ 771 * segments.length := by
  induction segments with
  | nil => simp [wireSegmentsProgram]
  | cons head tail ih =>
      have headBound := wireSegment_length head
      simp only [wireSegmentsProgram, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.length_append] at *
      simp only [List.length_cons]
      omega

/-- The standalone emitter returns its exact source wire and executed cost. -/
theorem wireSegments_run [BN254.FieldCertificate] (segments : List WireSegment)
    (fits : (wireSegmentsProgram segments).length < 2 ^ 256) (memory : Memory) :
    let machine := linearMachine (wireSegmentsProgram segments) fits
    (run machine ((wireSegmentsProgram segments).length + 1)
      ⟨⟨0, by simp [machine, linearMachine]⟩, memory⟩).map
      (Option.map fun result => (result.1.memory.bits 3, result.1.memory.ram, result.2)) =
      PMF.pure (some (segments.flatMap (WireSegment.wire memory.ram (memory.registers 11)) ++ memory.bits 3,
        memory.ram, (wireSegmentsProgram segments).length + 1)) := by
  dsimp only
  rw [linearMachine_run, PMF.pure_map]
  simp [wireSegments_bits, (wireSegments_preserves segments memory).1]

/-- The total cost includes the program table and every executed instruction. -/
theorem wireSegments_budget (segments : List WireSegment)
    (fits : (wireSegmentsProgram segments).length < 2 ^ 256) :
    (linearMachine (wireSegmentsProgram segments) fits).size + 1 +
      ((wireSegmentsProgram segments).length + 1) ≤ 1542 * segments.length + 2 := by
  have bound := wireSegments_length segments
  change (wireSegmentsProgram segments).length + 1 +
    ((wireSegmentsProgram segments).length + 1) ≤ _
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
