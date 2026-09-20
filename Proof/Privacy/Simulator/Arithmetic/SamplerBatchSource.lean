import Proof.Privacy.Simulator.Arithmetic.SamplerBatchMemory
import Proof.Privacy.Simulator.Arithmetic.PrivateSchedule

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The RAM source law stores each scheduled draw at its indexed address. -/
noncomputable def batchRamLaw {count : Nat} (plan : Vector DrawSpec count) (attempts : Nat)
    (pointer : Word) : Nat → Nat → (Word → Word) → PMF (Word → Word)
  | 0, _, ram => PMF.pure ram
  | remaining + 1, index, ram =>
      if inside : index < count then
        (drawSpecLaw attempts plan[index]).bind fun word =>
          batchRamLaw plan attempts pointer remaining (index + 1)
            (Function.update ram (pointer + BitVec.ofNat 256 index) word)
      else PMF.pure ram

/-- The exact machine memory law has the scheduled RAM source law. -/
theorem samplerBatchMemory_ram_source [BN254.FieldCertificate] {count : Nat}
    (plan : Vector DrawSpec count) (attempts remaining index : Nat) (base : Memory) :
    (samplerBatchMemory plan attempts remaining index base).map (fun result => result.1.ram) =
      batchRamLaw plan attempts (base.registers 10) remaining index base.ram := by
  induction remaining generalizing index base with
  | zero => simp [samplerBatchMemory, batchRamLaw, PMF.pure_map]
  | succ remaining ih =>
      by_cases inside : index < count
      · rw [samplerBatchMemory, dif_pos inside, PMF.map_bind, batchRamLaw, dif_pos inside]
        calc
          _ = (batchStepMemory plan[index] attempts index base).bind (fun result =>
            batchRamLaw plan attempts (base.registers 10) remaining (index + 1)
              (Function.update base.ram (base.registers 10 + BitVec.ofNat 256 index) (result.1.registers 0))) := by
                apply Security.ThreePhase.bind_eq_on_support
                intro result supported
                rcases result with ⟨memory, cost⟩
                simp only [PMF.map_comp, Function.comp_def]
                rw [ih]
                rw [batchStepMemory_caller _ attempts index base memory cost 10 (by decide) supported,
                  batchStepMemory_ram _ attempts index base memory cost supported]
          _ = _ := by
            have source := batchStepMemory_source plan[index] attempts index base
            change (batchStepMemory plan[index] attempts index base).map (fun result => result.1.registers 0) =
              drawSpecLaw attempts plan[index] at source
            rw [← source, PMF.bind_map]
            rfl
      · simp [samplerBatchMemory, batchRamLaw, inside, PMF.pure_map]

/-- The word writer uses one successive address for each source word. -/
def storeDrawWords (pointer : Word) : Nat → (Word → Word) → List Word → (Word → Word)
  | _, ram, [] => ram
  | index, ram, word :: rest => storeDrawWords pointer (index + 1)
      (Function.update ram (pointer + BitVec.ofNat 256 index) word) rest

/-- A suffix schedule gives the exact RAM law for the same fixed range of entries. -/
theorem batchRamLaw_list {count : Nat} (plan : Vector DrawSpec count) (attempts : Nat) (pointer : Word)
    (remaining index : Nat) (ram : Word → Word) (within : index + remaining ≤ count) :
    batchRamLaw plan attempts pointer remaining index ram =
      (drawPlanLaw attempts ((plan.toList.drop index).take remaining)).map (storeDrawWords pointer index ram) := by
  induction remaining generalizing index ram with
  | zero => simp [batchRamLaw, drawPlanLaw, storeDrawWords, PMF.pure_map]
  | succ remaining ih =>
      have inside : index < count := by omega
      have listInside : index < plan.toList.length := by simpa using inside
      have dropped : plan.toList.drop index = plan[index] :: plan.toList.drop (index + 1) := by
        exact List.drop_eq_getElem_cons listInside
      rw [batchRamLaw, dif_pos inside, dropped, List.take_succ_cons, drawPlanLaw, PMF.map_bind]
      apply congrArg (fun continuation => (drawSpecLaw attempts plan[index]).bind continuation)
      funext word
      rw [ih (index + 1) _ (by omega)]
      simp only [PMF.map_comp, Function.comp_def, storeDrawWords]

/-- The complete batch stores exactly the flat source word list. -/
theorem samplerBatchMemory_source [BN254.FieldCertificate] {count : Nat}
    (plan : Vector DrawSpec count) (attempts : Nat) (base : Memory) :
    (samplerBatchMemory plan attempts count 0 base).map (fun result => result.1.ram) =
      (drawPlanLaw attempts plan.toList).map (storeDrawWords (base.registers 10) 0 base.ram) := by
  rw [samplerBatchMemory_ram_source, batchRamLaw_list plan attempts (base.registers 10) count 0 base.ram (by omega)]
  simp only [List.drop_zero, List.take_of_length_le (by simp : plan.toList.length ≤ count)]

/-- The complete offline plan has a fixed vector size without literal instruction expansion. -/
def offlinePlan : Vector DrawSpec 838208 := ⟨offlineSchedule.plan.toArray, by
  simpa using offlineSchedule_length⟩

/-- The complete offline machine stores the exact total private coin representation. -/
theorem offlineMemory_source [BN254.FieldCertificate] (attempts : Nat) (base : Memory) :
    (samplerBatchMemory offlinePlan attempts 838208 0 base).map (fun result => result.1.ram) =
      (Security.SimulatorSampling.offline.total attempts).law.map
        (fun coin => storeDrawWords (base.registers 10) 0 base.ram (offlineSchedule.words coin)) := by
  rw [samplerBatchMemory_source]
  have planList : offlinePlan.toList = offlineSchedule.plan := by simp [offlinePlan]
  rw [planList, offlineSchedule_source, PMF.map_comp]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
