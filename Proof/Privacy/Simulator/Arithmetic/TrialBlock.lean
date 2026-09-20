import Proof.Privacy.Simulator.Arithmetic.IntegerTrial

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host contains each trial instruction before the return label. -/
def ContainsTrial (host : Machine) (width : Nat) (bound : Word) (full : Bool)
    (labels : Fin 20 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 20, pc.val < 19 → host.code[(labels pc).val] =
    relocate labels ((integerTrial width bound full).code[pc.val]'(by exact pc.isLt))

/-- Two assembly passes compose their label maps. -/
theorem relocate_comp {a b c : Nat} (first : Fin a → Fin b) (second : Fin b → Fin c)
    (instruction : Instruction a) :
    relocate second (relocate first instruction) = relocate (second ∘ first) instruction := by
  cases instruction <;> rfl

/-- The embedded trial retains the low-word sampler. -/
theorem trialBlock_word (host : Machine) (width : Nat) (bound : Word) (full : Bool)
    (labels : Fin 20 → Fin (host.size + 1)) (present : ContainsTrial host width bound full labels) :
    ContainsWordSampler host width (labels ∘ trialLabels) := by
  intro pc inside
  have selected := present (trialLabels pc) (by simpa [trialLabels] using Nat.lt_trans inside (by decide : 12 < 19))
  simp [integerTrial, trialLabels, inside] at selected
  exact selected.trans (relocate_comp trialLabels labels _)

/-- The narrow comparison returns control after three instructions. -/
theorem trialBlock_narrow_tail [BN254.FieldCertificate] (host : Machine) (width : Nat)
    (bound : Word) (labels : Fin 20 → Fin (host.size + 1))
    (present : ContainsTrial host width bound false labels) (base : Memory) (value : Word) :
    runPrefix host 3 ⟨labels 12, frame base value 0 0⟩ =
      PMF.pure (some (false, ⟨labels 19, narrowTrialFrame base value bound⟩, 3)) := by
  simp [runPrefix, step, present 12 (by decide), present 17 (by decide), present 18 (by decide),
    integerTrial, relocate, frame, wideFrame, narrowTrialFrame, Arithmetic.eval,
    PMF.pure_map, Function.update_comm]

/-- The narrow trial returns its comparison flag without executing the host continuation. -/
theorem trialBlock_narrow [BN254.FieldCertificate] (host : Machine) (width : Nat)
    (bound : Word) (labels : Fin 20 → Fin (host.size + 1))
    (present : ContainsTrial host width bound false labels) (base : Memory) (fits : width ≤ 256) :
    runPrefix host (7 * width + 8) ⟨labels 0, base⟩ =
      (coinFold width 0).map fun value =>
        some (false, ⟨labels 19, narrowTrialFrame base value bound⟩, 7 * width + 8) := by
  rw [show 7 * width + 8 = (7 * width + 5) + 3 by omega, prefix_add]
  change (runPrefix host (7 * width + 5) ⟨(labels ∘ trialLabels) 0, base⟩).bind _ = _
  rw [wordBlock_prefix host width (labels ∘ trialLabels)
    (trialBlock_word host width bound false labels present) base fits]
  simp only [PMF.bind_map, Function.comp_def]
  change (coinFold width 0).bind (fun value =>
    (runPrefix host 3 ⟨labels 12, frame base value 0 0⟩).map _) = _
  change (coinFold width 0).bind _ = (coinFold width 0).bind _
  congr 1
  funext value
  rw [trialBlock_narrow_tail host width bound labels present base value]
  simp [PMF.pure_map, Nat.add_comm]

/-- The full-range comparison returns control after four instructions. -/
theorem trialBlock_full_tail [BN254.FieldCertificate] (host : Machine) (width : Nat)
    (bound : Word) (labels : Fin 20 → Fin (host.size + 1))
    (present : ContainsTrial host width bound true labels) (base : Memory) (value : Word) :
    runPrefix host 4 ⟨labels 12, frame base value 0 0⟩ =
      (PMF.uniformOfFintype Bool).map fun bit =>
        some (false, ⟨labels 19, fullTrialFrame base value bit⟩, 4) := by
  simp [runPrefix, step, present 12 (by decide), present 13 (by decide),
    integerTrial, relocate, frame, Function.update, PMF.map_bind, PMF.bind_bind]
  congr 1
  funext bit
  cases bit <;> simp [present 14 (by decide), present 15 (by decide), present 16 (by decide),
    integerTrial, relocate, Arithmetic.eval, PMF.pure_map, fullTrialFrame, wideFrame, frame,
    Function.update_comm]

/-- The full-range trial returns its low word, high bit, and comparison flag. -/
theorem trialBlock_full [BN254.FieldCertificate] (host : Machine) (bound : Word)
    (labels : Fin 20 → Fin (host.size + 1))
    (present : ContainsTrial host 256 bound true labels) (base : Memory) :
    runPrefix host 1801 ⟨labels 0, base⟩ =
      (PMF.uniformOfFintype Word).bind fun value =>
        (PMF.uniformOfFintype Bool).map fun bit =>
          some (false, ⟨labels 19, fullTrialFrame base value bit⟩, 1801) := by
  rw [show 1801 = (7 * 256 + 5) + 4 from rfl, prefix_add]
  change (runPrefix host (7 * 256 + 5) ⟨(labels ∘ trialLabels) 0, base⟩).bind _ = _
  rw [wordBlock_prefix host 256 (labels ∘ trialLabels)
    (trialBlock_word host 256 bound true labels present) base (by decide), coinFold_word_uniform]
  simp only [PMF.bind_map, Function.comp_def]
  congr 1
  funext value
  change (runPrefix host 4 ⟨labels 12, frame base value 0 0⟩).map _ = _
  rw [trialBlock_full_tail host 256 bound labels present base value]
  simp only [PMF.map_comp, Function.comp_def, Option.map_some]

end Kriterion.ArgoMAC.ArithmeticSimulator
