import Proof.Privacy.Simulator.Arithmetic.PointBatchMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each boundary names the next point draw or the caller's return. -/
def pointBatchBoundary {count : Nat} (index : Nat) (inside : index ≤ count) : Fin (58 * count + 1) :=
  ⟨58 * index, by omega⟩

/-- The host contains every point-batch instruction before its return. -/
def ContainsPointBatch (host : Machine) (count attempts : Nat) (fits : 58 * count < 2 ^ 256)
    (labels : Fin (58 * count + 1) → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin (58 * count + 1), pc.val < 58 * count →
    host.code[(labels pc).val] = relocate labels ((pointBatch count attempts fits).code[pc.val])

/-- Each point entry contains the complete private point sampler. -/
theorem pointBatchBlock_contains (host : Machine) (count attempts : Nat) (fits : 58 * count < 2 ^ 256)
    (labels : Fin (58 * count + 1) → Fin (host.size + 1))
    (present : ContainsPointBatch host count attempts fits labels) (index : Fin count) :
    ContainsPointSampler host attempts (labels ∘ pointBatchLabels index) := by
  intro pc inside
  have i := index.isLt
  have p := pc.isLt
  have position : 58 * index.val + pc.val < 58 * count := by omega
  have quotient : (58 * index.val + pc.val) / 58 = index.val := by omega
  have remainder : (58 * index.val + pc.val) % 58 = pc.val := by omega
  have source : (pointBatch count attempts fits).code[(pointBatchLabels index pc).val] =
      relocate (pointBatchLabels index) ((pointSampler attempts).code[pc.val]'(by exact pc.isLt)) := by
    simp [pointBatch, pointBatchLabels, position, quotient, remainder, inside]
    rfl
  exact ((present (pointBatchLabels index pc) position).trans (congrArg (relocate labels) source)).trans
    (relocate_comp (pointBatchLabels index) labels _)

/-- The host writes the point in canonical form and stores its three words. -/
theorem pointBatchBlock_store [BN254.FieldCertificate] (host : Machine) (count attempts : Nat)
    (fits : 58 * count < 2 ^ 256) (labels : Fin (58 * count + 1) → Fin (host.size + 1))
    (present : ContainsPointBatch host count attempts fits labels) (index : Fin count) (fuel : Nat) (base : Memory)
    (valid : readPoint base.registers scalarAccumulator = some (pointValue base)) :
    run host (fuel + 11) ⟨labels (pointBatchLabels index 47), base⟩ =
      (run host fuel ⟨labels (pointBatchBoundary (index.val + 1) index.isLt), pointStored base index.val⟩).map
        (Option.map fun result => (result.1, result.2 + 11)) := by
  let slot (offset : Fin 58) : Fin (58 * count + 1) :=
    ⟨58 * index.val + offset.val, by have i := index.isLt; have o := offset.isLt; omega⟩
  have code (offset : Fin 58) (lower : 47 ≤ offset.val) :
      host.code[(labels (slot offset)).val] = relocate labels
        (if offset.val = 47 then .constant 5 0 (slot 48)
        else if offset.val = 48 then .pointAdd scalarAccumulator scalarAccumulator scalarMultiple (slot 49)
        else if offset.val = 49 then .constant 8 (BitVec.ofNat 256 (3 * index.val)) (slot 50)
        else if offset.val = 50 then .arithmetic .add 8 10 8 (slot 51)
        else if offset.val = 51 then .store 8 2 (slot 52)
        else if offset.val = 52 then .constant 8 (BitVec.ofNat 256 (3 * index.val + 1)) (slot 53)
        else if offset.val = 53 then .arithmetic .add 8 10 8 (slot 54)
        else if offset.val = 54 then .store 8 3 (slot 55)
        else if offset.val = 55 then .constant 8 (BitVec.ofNat 256 (3 * index.val + 2)) (slot 56)
        else if offset.val = 56 then .arithmetic .add 8 10 8 (slot 57)
        else .store 8 4 (pointBatchBoundary (index.val + 1) index.isLt)) := by
    have i := index.isLt
    have o := offset.isLt
    have inside : 58 * index.val + offset.val < 58 * count := by omega
    have quotient : (58 * index.val + offset.val) / 58 = index.val := by omega
    have remainder : (58 * index.val + offset.val) % 58 = offset.val := by omega
    rw [present (slot offset) inside]
    apply congrArg (relocate labels)
    simp [pointBatch, slot, pointBatchBoundary, inside, quotient, remainder,
      show ¬offset.val < 47 by omega]
  have readAcc : readPoint (Function.update base.registers 5 0#256) scalarAccumulator = some (pointValue base) := by
    rw [readPoint_update_other base.registers scalarAccumulator 5 0#256 (by decide) (by decide) (by decide)]
    exact valid
  have readZero : readPoint (Function.update base.registers 5 0#256) scalarMultiple = some (0 : BN254.Point) := by
    simp [readPoint, scalarMultiple]
  simp only [scalarAccumulator] at readAcc
  change run host (fuel + 11) ⟨labels (slot 47), base⟩ = _
  cases point : pointValue base <;>
    simp [run, step, code 47 (by decide), code 48 (by decide), readAcc, readZero, code 49 (by decide), code 50 (by decide), code 51 (by decide), code 52 (by decide),
      code 53 (by decide), code 54 (by decide), code 55 (by decide), code 56 (by decide), code 57 (by decide),
      relocate, Arithmetic.eval, pointStored, pointCanonical, pointWords, storeDrawWords, point, writePoint,
      scalarAccumulator, Function.update_comm, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The host returns from one point draw with its exact unused fuel. -/
theorem pointBatchBlock_step [BN254.FieldCertificate] (host : Machine) (count attempts : Nat)
    (fits : 58 * count < 2 ^ 256) (labels : Fin (58 * count + 1) → Fin (host.size + 1))
    (present : ContainsPointBatch host count attempts fits labels) (index : Fin count) (fuel : Nat) (base : Memory)
    (countFits : attempts < 2 ^ 256) :
    run host (pointBatchStepBudget attempts + fuel)
      ⟨labels (pointBatchBoundary index.val (Nat.le_of_lt index.isLt)), base⟩ =
      (pointBatchStepMemory attempts index.val base).bind fun result =>
        (run host (pointBatchStepBudget attempts + fuel - result.2)
          ⟨labels (pointBatchBoundary (index.val + 1) index.isLt), result.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2)) := by
  have continued := pointSamplerBlock_run host attempts (labels ∘ pointBatchLabels index)
    (pointBatchBlock_contains host count attempts fits labels present index) (11 + fuel) base countFits
  have sameFuel : pointBatchStepBudget attempts + fuel = pointSamplerFuel attempts - 1 + (11 + fuel) := by
    unfold pointBatchStepBudget
    omega
  conv_lhs => rw [sameFuel]
  change run host (pointSamplerFuel attempts - 1 + (11 + fuel))
    ⟨(labels ∘ pointBatchLabels index) 0, base⟩ = _
  rw [continued, pointBatchStepMemory, PMF.bind_map]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨memory, cost⟩
  have bounded := pointSamplerReturnMemory_cost attempts base memory cost supported
  have amount : pointSamplerFuel attempts - 1 + (11 + fuel) - cost =
      (pointBatchStepBudget attempts + fuel - (cost + 11)) + 11 := by unfold pointBatchStepBudget; omega
  change (run host (pointSamplerFuel attempts - 1 + (11 + fuel) - cost)
    ⟨labels (pointBatchLabels index 47), memory⟩).map _ = _
  rw [amount, pointBatchBlock_store host count attempts fits labels present index _ memory
    (pointSamplerReturnMemory_valid attempts base memory cost supported)]
  simp only [PMF.map_comp, Function.comp_def, Option.map_map]
  apply congrArg (fun transform => PMF.map transform
    (run host (pointBatchStepBudget attempts + fuel - (cost + 11))
      ⟨labels (pointBatchBoundary (index.val + 1) index.isLt), pointStored memory index.val⟩))
  funext outcome
  cases outcome <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Kriterion.ArgoMAC.ArithmeticSimulator
