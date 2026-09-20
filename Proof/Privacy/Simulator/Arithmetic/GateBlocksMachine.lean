import Construction.Simulator.GateBlocksMachine
import Proof.Privacy.Simulator.Arithmetic.GateBlocks
import Proof.Privacy.Simulator.Arithmetic.TrialBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- A host contains the complete gate-block branch machine before its return. -/
def ContainsGateBlocks (host : Machine) (tweak : Block) (labels : Fin 39 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 39, pc.val < 38 → host.code[(labels pc).val] = relocate labels ((gateBlocksMachine tweak).code[pc.val])

private theorem relocate_linear {source target : Nat} (labels : Fin source → Fin target)
    (instruction : LinearInstruction) (next : Fin source) :
    relocate labels (instruction.emit next) = instruction.emit (labels next) := by cases instruction <;> rfl

/-- The gate-block host contains the entire hash branch. -/
theorem gateBlocks_hash (host : Machine) (tweak : Block) (labels : Fin 39 → Fin (host.size + 1))
    (present : ContainsGateBlocks host tweak labels) : ContainsLinear host (gateHashProgram tweak) (labels ∘ gateHashLabels) := by
  intro index inside
  have small : index < 27 := by simpa only [gateHashProgram_length] using inside
  have position : (gateHashLabels index).val < 38 := by simp [gateHashLabels, small]; omega
  have source : (gateBlocksMachine tweak).code[(gateHashLabels index).val] =
      ((gateHashProgram tweak)[index]).emit (gateHashLabels (index + 1)) := by
    simp only [gateBlocksMachine, Vector.getElem_ofFn, gateHashLabels, dif_pos small]
    rw [dif_neg (by omega : ¬ 1 + index = 0), dif_pos (by omega : 1 + index < 28)]
    simp only [Nat.add_sub_cancel_left]
    rfl
  exact ((present (gateHashLabels index) position).trans (congrArg (relocate labels) source)).trans
    (relocate_linear labels _ _)

/-- The gate-block host contains the entire pad branch. -/
theorem gateBlocks_pad (host : Machine) (tweak : Block) (labels : Fin 39 → Fin (host.size + 1))
    (present : ContainsGateBlocks host tweak labels) : ContainsLinear host (gatePadProgram tweak) (labels ∘ gatePadLabels) := by
  intro index inside
  have small : index < 10 := by simpa only [gatePadProgram_length] using inside
  have position : (gatePadLabels index).val < 38 := by simp [gatePadLabels, small]; omega
  have source : (gateBlocksMachine tweak).code[(gatePadLabels index).val] =
      ((gatePadProgram tweak)[index]).emit (gatePadLabels (index + 1)) := by
    simp only [gateBlocksMachine, Vector.getElem_ofFn, gatePadLabels, dif_pos small]
    rw [dif_neg (by omega : ¬ 28 + index = 0), dif_neg (by omega : ¬ 28 + index < 28),
      dif_pos (by omega : 28 + index < 38)]
    simp only [Nat.add_sub_cancel_left]
    rfl
  exact ((present (gatePadLabels index) position).trans (congrArg (relocate labels) source)).trans
    (relocate_linear labels _ _)

/-- The branch memory has the exact selected source program. -/
def gateBlocksMemory (tweak : Block) (bit : Bool) (base : Memory) : Memory :=
  executeLinear (if bit then gatePadProgram tweak else gateHashProgram tweak) base

/-- The branch charge includes the selector and every selected arithmetic instruction. -/
def gateBlocksCost (bit : Bool) : Nat := if bit then 11 else 28

/-- The host gate block returns the exact selected memory and full instruction charge. -/
theorem gateBlocksHost_continue [BN254.FieldCertificate] (host : Machine) (tweak : Block)
    (labels : Fin 39 → Fin (host.size + 1)) (present : ContainsGateBlocks host tweak labels)
    (base : Memory) (bit : Bool) (encoded : base.registers 10 = if bit then 1 else 0) (fuel : Nat) :
    run host (fuel + gateBlocksCost bit) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels 38, gateBlocksMemory tweak bit base⟩).map
        (Option.map fun result => (result.1, result.2 + gateBlocksCost bit)) := by
  have branch := present 0 (by decide)
  have first : (gateBlocksMachine tweak).code[0]'(by change 0 < 39; decide) = .branch 10 1 28 := by
    simp only [gateBlocksMachine, Vector.getElem_ofFn]
    rfl
  change host.code[(labels 0).val] = relocate labels ((gateBlocksMachine tweak).code[0]'(by change 0 < 39; decide)) at branch
  rw [first] at branch
  change host.code[(labels 0).val] = .branch 10 (labels 1) (labels 28) at branch
  cases bit
  · have linear := linear_continue host (gateHashProgram tweak) (labels ∘ gateHashLabels)
      (gateBlocks_hash host tweak labels present) base fuel
    simp only [gateHashProgram_length] at linear
    change run host (27 + fuel) ⟨labels 1, base⟩ =
      (run host fuel ⟨labels 38, executeLinear (gateHashProgram tweak) base⟩).map
        (Option.map fun result => (result.1, result.2 + 27)) at linear
    simp only [gateBlocksCost, Bool.false_eq_true, ↓reduceIte] at encoded ⊢
    rw [show fuel + 28 = (fuel + 27) + 1 by omega]
    rw [run]
    simp only [step, branch, encoded, ↓reduceIte, PMF.pure_bind]
    rw [show fuel + 27 = 27 + fuel by omega, linear]
    simp [gateBlocksMemory, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]
  · have linear := linear_continue host (gatePadProgram tweak) (labels ∘ gatePadLabels)
      (gateBlocks_pad host tweak labels present) base fuel
    simp only [gatePadProgram_length] at linear
    change run host (10 + fuel) ⟨labels 28, base⟩ =
      (run host fuel ⟨labels 38, executeLinear (gatePadProgram tweak) base⟩).map
        (Option.map fun result => (result.1, result.2 + 10)) at linear
    simp only [gateBlocksCost, ↓reduceIte] at encoded ⊢
    rw [show fuel + 11 = (fuel + 10) + 1 by omega]
    rw [run]
    simp only [step, branch, encoded, show (1 : Word) ≠ 0 by decide, ↓reduceIte, PMF.pure_bind]
    rw [show fuel + 10 = 10 + fuel by omega, linear]
    simp [gateBlocksMemory, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The branch machine charges its full table and at most 29 executed steps. -/
theorem gateBlocksMachine_budget (tweak : Block) (bit : Bool) :
    (gateBlocksMachine tweak).size + 1 + (gateBlocksCost bit + 1) ≤ 68 := by
  change 38 + 1 + (gateBlocksCost bit + 1) ≤ 68
  cases bit <;> decide

end Kriterion.ArgoMAC.ArithmeticSimulator
