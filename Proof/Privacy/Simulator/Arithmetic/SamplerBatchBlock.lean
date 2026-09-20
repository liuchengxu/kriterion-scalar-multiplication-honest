import Proof.Privacy.Simulator.Arithmetic.SamplerBatchMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each boundary names the next draw or the caller's return. -/
def batchBoundary {count : Nat} (index : Nat) (inside : index ≤ count) : Fin (39 * count + 1) :=
  ⟨39 * index, by omega⟩

/-- A host contains every batch instruction before its return. -/
def ContainsSamplerBatch {count : Nat} (host : Machine) (plan : Vector DrawSpec count) (attempts : Nat)
    (fits : 39 * count < 2 ^ 256) (labels : Fin (39 * count + 1) → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin (39 * count + 1), pc.val < 39 * count →
    host.code[(labels pc).val] = relocate labels ((samplerBatch plan attempts fits).code[pc.val])

/-- The host contains the total sampler at each scheduled draw. -/
theorem samplerBatchBlock_contains {count : Nat} (host : Machine) (plan : Vector DrawSpec count)
    (attempts : Nat) (fits : 39 * count < 2 ^ 256) (labels : Fin (39 * count + 1) → Fin (host.size + 1))
    (present : ContainsSamplerBatch host plan attempts fits labels) (index : Fin count) :
    ContainsTotalSampler host attempts plan[index].2 (labels ∘ batchSamplerLabels index) := by
  intro pc inside
  have selected := present (batchSamplerLabels index pc) (by
    change 39 * index.val + 1 + pc.val < 39 * count
    have i := index.isLt
    omega)
  exact (selected.trans (congrArg (relocate labels) (samplerBatch_contains plan attempts fits index pc inside))).trans
    (relocate_comp (batchSamplerLabels index) labels _)

/-- The host loads the next runtime range in one instruction. -/
theorem samplerBatchBlock_entry [BN254.FieldCertificate] {count : Nat} (host : Machine)
    (plan : Vector DrawSpec count) (attempts : Nat) (fits : 39 * count < 2 ^ 256)
    (labels : Fin (39 * count + 1) → Fin (host.size + 1))
    (present : ContainsSamplerBatch host plan attempts fits labels) (index : Fin count) (fuel : Nat) (base : Memory) :
    run host (fuel + 1) ⟨labels (batchBoundary index.val (Nat.le_of_lt index.isLt)), base⟩ =
      (run host fuel ⟨labels (batchSamplerLabels index 0),
        {base with registers := Function.update base.registers 5 plan[index].1}⟩).map
        (Option.map fun result => (result.1, result.2 + 1)) := by
  have selected := present (batchBoundary index.val (Nat.le_of_lt index.isLt)) (by
    change 39 * index.val < 39 * count
    have i := index.isLt
    omega)
  change host.code[(labels (batchBoundary index.val (Nat.le_of_lt index.isLt))).val] =
    relocate labels ((samplerBatch plan attempts fits).code[39 * index.val]'(by
      change 39 * index.val < 39 * count + 1
      have i := index.isLt
      omega)) at selected
  rw [samplerBatch_entry_code plan attempts fits index] at selected
  simp only [run, step, selected, relocate, PMF.pure_bind]

/-- The host stores the sampled word in three instructions. -/
theorem samplerBatchBlock_store [BN254.FieldCertificate] {count : Nat} (host : Machine)
    (plan : Vector DrawSpec count) (attempts : Nat) (fits : 39 * count < 2 ^ 256)
    (labels : Fin (39 * count + 1) → Fin (host.size + 1))
    (present : ContainsSamplerBatch host plan attempts fits labels) (index : Fin count) (fuel : Nat) (base : Memory) :
    run host (fuel + 3) ⟨labels (batchSamplerLabels index 35), base⟩ =
      (run host fuel ⟨labels (batchBoundary (index.val + 1) index.isLt), batchStored base index.val⟩).map
        (Option.map fun result => (result.1, result.2 + 3)) := by
  let slot (offset : Fin 39) : Fin (39 * count + 1) :=
    ⟨39 * index.val + offset.val, by have i := index.isLt; have o := offset.isLt; omega⟩
  have code (offset : Fin 39) (lower : 36 ≤ offset.val) :
      host.code[(labels (slot offset)).val] =
        relocate labels (if offset.val = 36 then .constant 8 (BitVec.ofNat 256 index.val) (slot 37)
        else if offset.val = 37 then .arithmetic .add 8 10 8 (slot 38)
        else .store 8 0 (batchBoundary (index.val + 1) index.isLt)) := by
    have i := index.isLt
    have o := offset.isLt
    have inside : 39 * index.val + offset.val < 39 * count := by omega
    have quotient : (39 * index.val + offset.val) / 39 = index.val := by omega
    have remainder : (39 * index.val + offset.val) % 39 = offset.val := by omega
    rw [present (slot offset) inside]
    apply congrArg (relocate labels)
    simp [samplerBatch, slot, batchBoundary, inside, quotient, remainder,
      show offset.val ≠ 0 by omega, show ¬offset.val < 36 by omega]
  change run host (fuel + 3) ⟨labels (slot 36), base⟩ = _
  simp [run, step, code 36 (by decide), code 37 (by decide), code 38 (by decide),
    relocate, Arithmetic.eval, batchStored, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The host completes one scheduled draw and keeps its exact unused fuel. -/
theorem samplerBatchBlock_step [BN254.FieldCertificate] {count : Nat} (host : Machine)
    (plan : Vector DrawSpec count) (attempts : Nat) (fits : 39 * count < 2 ^ 256)
    (labels : Fin (39 * count + 1) → Fin (host.size + 1))
    (present : ContainsSamplerBatch host plan attempts fits labels) (index : Fin count) (fuel : Nat) (base : Memory)
    (countFits : attempts < 2 ^ 256) :
    run host (batchStepBudget attempts + fuel)
      ⟨labels (batchBoundary index.val (Nat.le_of_lt index.isLt)), base⟩ =
      (batchStepMemory plan[index] attempts index.val base).bind fun result =>
        (run host (batchStepBudget attempts + fuel - result.2)
          ⟨labels (batchBoundary (index.val + 1) index.isLt), result.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2)) := by
  let reserve := (runtimeTrialCost plan[index].1 + 2) * attempts + 7
  have reserveBound : reserve + 4 ≤ batchStepBudget attempts := by
    have product := Nat.mul_le_mul_right attempts
      (show runtimeTrialCost plan[index].1 + 2 ≤ 2574 by have h := runtimeTrialCost_bound plan[index].1; omega)
    unfold reserve batchStepBudget
    omega
  conv_lhs => rw [show batchStepBudget attempts + fuel = (batchStepBudget attempts + fuel - 1) + 1 by omega]
  rw [samplerBatchBlock_entry host plan attempts fits labels present index]
  conv_lhs => rw [show batchStepBudget attempts + fuel - 1 =
    reserve + (batchStepBudget attempts + fuel - 1 - reserve) by omega]
  have continued := totalSamplerBlock_run host attempts plan[index].2 plan[index].1
    (labels ∘ batchSamplerLabels index) (samplerBatchBlock_contains host plan attempts fits labels present index)
    (batchStepBudget attempts + fuel - 1 - reserve)
    {base with registers := Function.update base.registers 5 plan[index].1} (by simp) countFits
  change run host (reserve + (batchStepBudget attempts + fuel - 1 - reserve))
    ⟨labels (batchSamplerLabels index 0), _⟩ = _ at continued
  rw [continued]
  rw [PMF.map_bind, batchStepMemory, PMF.bind_map]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨memory, cost⟩
  have bounded := totalSamplerMemory_cost plan[index].1 attempts plan[index].2 _ memory cost supported
  change cost ≤ reserve at bounded
  have amount : reserve + (batchStepBudget attempts + fuel - 1 - reserve) - cost =
      (batchStepBudget attempts + fuel - (cost + 4)) + 3 := by omega
  change ((run host (reserve + (batchStepBudget attempts + fuel - 1 - reserve) - cost)
    ⟨labels (batchSamplerLabels index 35), memory⟩).map _).map _ = _
  rw [amount, samplerBatchBlock_store host plan attempts fits labels present index]
  simp only [PMF.map_comp, Function.comp_def, Option.map_map]
  apply congrArg (fun transform => PMF.map transform
    (run host (batchStepBudget attempts + fuel - (cost + 4))
      ⟨labels (batchBoundary (index.val + 1) index.isLt), batchStored memory index.val⟩))
  funext outcome
  cases outcome <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The host executes any contiguous part of the fixed batch. -/
theorem samplerBatchBlock_run [BN254.FieldCertificate] {count : Nat} (host : Machine)
    (plan : Vector DrawSpec count) (attempts : Nat) (fits : 39 * count < 2 ^ 256)
    (labels : Fin (39 * count + 1) → Fin (host.size + 1))
    (present : ContainsSamplerBatch host plan attempts fits labels) (remaining index fuel : Nat) (base : Memory)
    (within : index + remaining ≤ count) (countFits : attempts < 2 ^ 256) :
    run host (batchStepBudget attempts * remaining + fuel)
      ⟨labels (batchBoundary index (by omega)), base⟩ =
      (samplerBatchMemory plan attempts remaining index base).bind fun result =>
        (run host (batchStepBudget attempts * remaining + fuel - result.2)
          ⟨labels (batchBoundary (index + remaining) within), result.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2)) := by
  induction remaining generalizing index fuel base with
  | zero =>
      simp only [samplerBatchMemory, PMF.pure_bind, Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.sub_zero]
      rw [show (Option.map fun final : Configuration (host.size + 1) × Nat => (final.1, final.2)) = id from by
        funext value; cases value <;> rfl, PMF.map_id]
  | succ remaining ih =>
      have inside : index < count := by omega
      let selected : Fin count := ⟨index, inside⟩
      conv_lhs => rw [show batchStepBudget attempts * (remaining + 1) + fuel =
        batchStepBudget attempts + (batchStepBudget attempts * remaining + fuel) by rw [Nat.mul_succ]; omega]
      rw [samplerBatchBlock_step host plan attempts fits labels present selected _ base countFits]
      conv_rhs => rw [samplerBatchMemory, dif_pos inside, PMF.bind_bind]
      apply Security.ThreePhase.bind_eq_on_support
      intro result supported
      rcases result with ⟨memory, cost⟩
      have bounded := batchStepMemory_cost plan[selected] attempts index base memory cost supported
      have amount : batchStepBudget attempts + (batchStepBudget attempts * remaining + fuel) - cost =
          batchStepBudget attempts * remaining + (batchStepBudget attempts + fuel - cost) := by omega
      rw [amount, ih (index + 1) (batchStepBudget attempts + fuel - cost) memory (by omega), PMF.map_bind,
        PMF.bind_map]
      apply Security.ThreePhase.bind_eq_on_support
      intro result supported
      rcases result with ⟨tail, spent⟩
      have tailBound := samplerBatchMemory_cost plan attempts remaining (index + 1) memory tail spent supported
      dsimp only
      have finalFuel : batchStepBudget attempts * remaining + (batchStepBudget attempts + fuel - cost) - spent =
          batchStepBudget attempts * (remaining + 1) + fuel - (spent + cost) := by rw [Nat.mul_succ]; omega
      rw [finalFuel]
      simp only [PMF.map_comp, Function.comp_def, Option.map_map]
      have sameIndex : index + 1 + remaining = index + (remaining + 1) := by omega
      have sameBoundary : batchBoundary (index + 1 + remaining) (by omega) =
          batchBoundary (index + (remaining + 1)) within := Fin.ext (by simp [batchBoundary, sameIndex])
      rw [sameBoundary]
      apply congrArg (fun transform => PMF.map transform
        (run host (batchStepBudget attempts * (remaining + 1) + fuel - (spent + cost))
          ⟨labels (batchBoundary (index + (remaining + 1)) within), tail⟩))
      funext outcome
      cases outcome <;> simp [Nat.add_assoc]

end Kriterion.ArgoMAC.ArithmeticSimulator
