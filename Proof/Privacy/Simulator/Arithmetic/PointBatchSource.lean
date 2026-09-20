import Proof.Privacy.Simulator.Arithmetic.PointBatchLoopMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each point occupies exactly three words. -/
theorem pointWords_length [BN254.FieldCertificate] (point : BN254.Point) : (pointWords point).length = 3 := by
  cases point <;> rfl

/-- A point vector occupies three words per element. -/
theorem pointVectorWords_length [BN254.FieldCertificate] {count : Nat} (points : Vector BN254.Point count) :
    (vectorWords pointWords points).length = 3 * count := by
  have lengths (values : List BN254.Point) : (values.flatMap pointWords).length = 3 * values.length := by
    induction values with
    | nil => simp
    | cons head tail ih => simp [ih, pointWords_length, Nat.mul_add, Nat.add_mul, Nat.add_comm]
  simpa [vectorWords] using lengths points.toList

/-- Appended word lists write to successive RAM addresses. -/
theorem storeDrawWords_append (pointer : Word) (index : Nat) (ram : Word → Word) (first second : List Word) :
    storeDrawWords pointer index ram (first ++ second) =
      storeDrawWords pointer (index + first.length) (storeDrawWords pointer index ram first) second := by
  induction first generalizing index ram with
  | nil => simp [storeDrawWords]
  | cons head tail ih => simp [storeDrawWords, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The source vector appends each total point draw after the preceding vector. -/
theorem pointVector_push_law [BN254.FieldCertificate] (attempts count : Nat) :
    ((Security.SimulatorSampling.point.vector (count + 1)).total attempts).law =
      ((Security.SimulatorSampling.point.vector count).total attempts).law.bind fun previous =>
        (Security.SimulatorSampling.point.total attempts).law.map fun point => previous.push point := by
  rw [Security.SimulatorSampling.Code.vector, totalCode_cast_law, totalCode_map_law]
  simp only [Security.SimulatorSampling.Code.pair, Security.SimulatorSampling.Code.total,
    Security.BoundedIntegerSampling.BitCode.bind_law, totalCode_map_law, PMF.map_bind, PMF.map_comp,
    Function.comp_def, Security.SimulatorSampling.vectorPushEquiv, Equiv.coe_fn_mk]

/-- The point batch stores the exact total source vector in canonical RAM words. -/
theorem pointBatchMemory_source [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts start count : Nat) (base : Memory) :
    (pointBatchMemory attempts start count base).map (fun result => result.1.ram) =
      ((Security.SimulatorSampling.point.vector count).total attempts).law.map
        (fun points => storeDrawWords (base.registers 10) (3 * start) base.ram (vectorWords pointWords points)) := by
  induction count with
  | zero =>
      simp only [pointBatchMemory, PMF.pure_map, Security.SimulatorSampling.Code.vector,
        totalCode_cast_law, Security.SimulatorSampling.Code.total, Security.BoundedIntegerSampling.BitCode.law]
      rfl
  | succ count ih =>
      let next (ram : Word → Word) := (Security.SimulatorSampling.point.total attempts).law.map
        (fun point => storeDrawWords (base.registers 10) (3 * (start + count)) ram (pointWords point))
      rw [pointBatchMemory, PMF.map_bind]
      calc
        _ = (pointBatchMemory attempts start count base).bind (fun result => next result.1.ram) := by
          apply Security.ThreePhase.bind_eq_on_support
          intro result supported
          rcases result with ⟨memory, cost⟩
          simp only [PMF.map_comp, Function.comp_def]
          rw [pointBatchStepMemory_source]
          rw [pointBatchMemory_caller attempts start count base memory cost 10 (by decide) supported]
        _ = ((pointBatchMemory attempts start count base).map (fun result => result.1.ram)).bind next := by
          rw [PMF.bind_map]
          rfl
        _ = _ := by
          rw [ih, PMF.bind_map, pointVector_push_law, PMF.map_bind]
          apply congrArg (fun continuation => ((Security.SimulatorSampling.point.vector count).total attempts).law.bind continuation)
          funext previous
          simp only [Function.comp_def, next, PMF.map_comp]
          apply congrArg (fun transform => (Security.SimulatorSampling.point.total attempts).law.map transform)
          funext point
          have appended : vectorWords pointWords (previous.push point) = vectorWords pointWords previous ++ pointWords point := by
            simp [vectorWords, Vector.toList_push]
          rw [appended, storeDrawWords_append, pointVectorWords_length]
          congr 1
          omega

end Kriterion.ArgoMAC.ArithmeticSimulator
