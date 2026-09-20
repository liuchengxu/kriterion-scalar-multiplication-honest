import Proof.Privacy.Simulator.Arithmetic.PublicHistoryCode
import Proof.Privacy.Simulator.Arithmetic.ByteOutputBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host retains the fixed linear history blocks. -/
theorem publicHistoryBlock_linear (host : Machine) (labels : Fin 35 → Fin (host.size + 1))
    (present : ContainsPublicHistory host labels) (program : List LinearInstruction)
    (block : Nat → Fin 35) (contained : ContainsLinear publicHistory program block)
    (inside : ∀ index, index < program.length → (block index).val < 34) :
    ContainsLinear host program (labels ∘ block) := by
  intro index valid
  exact (present (block index) (inside index valid)).trans
    ((congrArg (relocate labels) (contained index valid)).trans
      (LinearInstruction.relocate_emit labels _ _))

/-- The dispatcher retains the original external tag in scratch RAM. -/
def publicHistoryForwardReady (memory : Memory) : Memory :=
  { memory with registers := Function.update (Function.update memory.registers 15 49) 0 (memory.ram 49) }

def publicHistoryInverseReady (memory : Memory) : Memory :=
  let base := publicHistoryForwardReady memory
  { base with registers := Function.update (Function.update base.registers 1 1) 0 (memory.ram 49 - 1#256) }


/-- The common tail appends the ordered pair and restores the reply. -/
def publicHistoryFinished (memory : Memory) : Memory :=
  executeLinear publicHistoryRestore (historyAppended memory)

/-- The append and restore blocks use seventeen instructions in any host. -/
theorem publicHistoryBlock_finish [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 35 → Fin (host.size + 1)) (present : ContainsPublicHistory host labels)
    (memory : Memory) (fuel : Nat) :
    run host (17 + fuel) ⟨labels 17, memory⟩ =
      (run host fuel ⟨labels 34, publicHistoryFinished memory⟩).map
        (Option.map fun result => (result.1, result.2 + 17)) := by
  have append := publicHistoryBlock_linear host labels present historyAppend publicHistoryAppendLabels
    publicHistory_append (by
      intro index valid
      have bound : index < 15 := valid
      simp [publicHistoryAppendLabels, publicHistoryLabels, bound]
      omega)
  have restore := publicHistoryBlock_linear host labels present publicHistoryRestore publicHistoryRestoreLabels
    publicHistory_restore (by
      intro index valid
      have bound : index < 2 := valid
      simp [publicHistoryRestoreLabels, publicHistoryLabels, bound]
      omega)
  have first := historyAppend_continue host (labels ∘ publicHistoryAppendLabels) append memory (2 + fuel)
  change run host (15 + (2 + fuel)) ⟨labels 17, memory⟩ = _ at first
  rw [show 17 + fuel = 15 + (2 + fuel) by omega, first]
  have second := linear_continue host publicHistoryRestore (labels ∘ publicHistoryRestoreLabels)
    restore (historyAppended memory) fuel
  change run host (2 + fuel) ⟨labels 32, historyAppended memory⟩ = _ at second
  change (run host (2 + fuel) ⟨labels 32, historyAppended memory⟩).map _ = _
  rw [second]
  simp [publicHistoryFinished, PMF.map_comp, Option.map_map, Function.comp_def,
    publicHistoryRestoreLabels, publicHistoryLabels, Nat.add_assoc,
    show publicHistoryRestore.length = 2 from rfl]

/-- The forward dispatch uses four instructions and preserves RAM and stacks. -/
theorem publicHistoryBlock_forwardDispatch [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 35 → Fin (host.size + 1)) (present : ContainsPublicHistory host labels)
    (memory : Memory) (accepted : memory.registers 7 ≠ 0#256) (tag : memory.ram 49#256 = 0#256) :
    runPrefix host 4 ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels 7, publicHistoryForwardReady memory⟩, 4)) := by
  simp [runPrefix, step, present 0 (by decide), present 1 (by decide), present 2 (by decide),
    present 3 (by decide), publicHistory, relocate, accepted, tag, publicHistoryForwardReady,
    PMF.pure_map, show (0 : Word) = 0#256 from rfl]

/-- The inverse dispatch uses seven instructions and preserves RAM and stacks. -/
theorem publicHistoryBlock_inverseDispatch [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 35 → Fin (host.size + 1)) (present : ContainsPublicHistory host labels)
    (memory : Memory) (accepted : memory.registers 7 ≠ 0#256) (tag : memory.ram 49#256 = 1#256) :
    runPrefix host 7 ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels 13, publicHistoryInverseReady memory⟩, 7)) := by
  simp [runPrefix, step, present 0 (by decide), present 1 (by decide), present 2 (by decide),
    present 3 (by decide), present 4 (by decide), present 5 (by decide), present 6 (by decide),
    publicHistory, relocate, accepted, tag, publicHistoryInverseReady, publicHistoryForwardReady,
    Arithmetic.eval, PMF.pure_map, show (0 : Word) = 0#256 from rfl]

/-- The accepted forward query appends its pair and returns the actual reply. -/
theorem publicHistoryBlock_forward [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 35 → Fin (host.size + 1)) (present : ContainsPublicHistory host labels)
    (memory : Memory) (fuel : Nat)
    (accepted : memory.registers 7 ≠ 0#256) (tag : memory.ram 49#256 = 0#256) :
    run host (27 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 34,
        publicHistoryFinished (executeLinear publicHistoryForward (publicHistoryForwardReady memory))⟩).map
          (Option.map fun result => (result.1, result.2 + 27)) := by
  have block := publicHistoryBlock_linear host labels present publicHistoryForward publicHistoryForwardLabels
    publicHistory_forward (by
      intro index valid
      have bound : index < 6 := valid
      simp [publicHistoryForwardLabels, publicHistoryLabels, bound]
      omega)
  rw [show 27 + fuel = 4 + (6 + (17 + fuel)) by omega, run_after_prefix,
    publicHistoryBlock_forwardDispatch host labels present memory accepted tag, PMF.pure_bind]
  have prepared := linear_continue host publicHistoryForward (labels ∘ publicHistoryForwardLabels)
    block (publicHistoryForwardReady memory) (17 + fuel)
  change run host (6 + (17 + fuel)) ⟨labels 7, publicHistoryForwardReady memory⟩ = _ at prepared
  dsimp only
  rw [prepared]
  change ((run host (17 + fuel) ⟨labels 17, _⟩).map _).map _ = _
  rw [publicHistoryBlock_finish host labels present]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc,
    show publicHistoryForward.length = 6 from rfl, show publicHistoryInverse.length = 4 from rfl]

/-- The accepted inverse query appends its pair and returns the actual reply. -/
theorem publicHistoryBlock_inverse [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 35 → Fin (host.size + 1)) (present : ContainsPublicHistory host labels)
    (memory : Memory) (fuel : Nat)
    (accepted : memory.registers 7 ≠ 0#256) (tag : memory.ram 49#256 = 1#256) :
    run host (28 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 34,
        publicHistoryFinished (executeLinear publicHistoryInverse (publicHistoryInverseReady memory))⟩).map
          (Option.map fun result => (result.1, result.2 + 28)) := by
  have block := publicHistoryBlock_linear host labels present publicHistoryInverse publicHistoryInverseLabels
    publicHistory_inverse (by
      intro index valid
      have bound : index < 4 := valid
      simp [publicHistoryInverseLabels, publicHistoryLabels, bound]
      omega)
  rw [show 28 + fuel = 7 + (4 + (17 + fuel)) by omega, run_after_prefix,
    publicHistoryBlock_inverseDispatch host labels present memory accepted tag, PMF.pure_bind]
  have prepared := linear_continue host publicHistoryInverse (labels ∘ publicHistoryInverseLabels)
    block (publicHistoryInverseReady memory) (17 + fuel)
  change run host (4 + (17 + fuel)) ⟨labels 13, publicHistoryInverseReady memory⟩ = _ at prepared
  dsimp only
  rw [prepared]
  change ((run host (17 + fuel) ⟨labels 17, _⟩).map _).map _ = _
  rw [publicHistoryBlock_finish host labels present]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc,
    show publicHistoryForward.length = 6 from rfl, show publicHistoryInverse.length = 4 from rfl]

/-- The cutoff path returns without a history write. -/
theorem publicHistoryBlock_rejected [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 35 → Fin (host.size + 1)) (present : ContainsPublicHistory host labels)
    (memory : Memory) (fuel : Nat) (rejected : memory.registers 7 = 0#256) :
    run host (1 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 34, memory⟩).map
        (Option.map fun result => (result.1, result.2 + 1)) := by
  rw [Nat.add_comm 1 fuel, run]
  simp [step, present 0 (by decide), publicHistory, relocate, rejected,
    show (0 : Word) = 0#256 from rfl]

/-- The non-fixed query path returns without a history write. -/
theorem publicHistoryBlock_otherDispatch [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 35 → Fin (host.size + 1)) (present : ContainsPublicHistory host labels)
    (memory : Memory) (accepted : memory.registers 7 ≠ 0#256)
    (notForward : memory.ram 49#256 ≠ 0#256) (notInverse : memory.ram 49#256 ≠ 1#256) :
    runPrefix host 7 ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels 34, publicHistoryInverseReady memory⟩, 7)) := by
  have subNonzero : memory.ram 49#256 - 1#256 ≠ 0#256 := by
    intro equal
    apply notInverse
    have same := congrArg (fun word : Word => word + 1#256) equal
    simpa only [BitVec.sub_add_cancel, BitVec.zero_add] using same
  simp [runPrefix, step, present 0 (by decide), present 1 (by decide), present 2 (by decide),
    present 3 (by decide), present 4 (by decide), present 5 (by decide), present 6 (by decide),
    publicHistory, relocate, accepted, notForward, notInverse, subNonzero,
    publicHistoryInverseReady, publicHistoryForwardReady, Arithmetic.eval, PMF.pure_map,
    show (0 : Word) = 0#256 from rfl]

/-- The non-fixed query path keeps the caller continuation and charges seven instructions. -/
theorem publicHistoryBlock_other [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 35 → Fin (host.size + 1)) (present : ContainsPublicHistory host labels)
    (memory : Memory) (fuel : Nat) (accepted : memory.registers 7 ≠ 0#256)
    (notForward : memory.ram 49#256 ≠ 0#256) (notInverse : memory.ram 49#256 ≠ 1#256) :
    run host (7 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 34, publicHistoryInverseReady memory⟩).map
        (Option.map fun result => (result.1, result.2 + 7)) := by
  rw [run_after_prefix,
    publicHistoryBlock_otherDispatch host labels present memory accepted notForward notInverse,
    PMF.pure_bind]

end Kriterion.ArgoMAC.ArithmeticSimulator
