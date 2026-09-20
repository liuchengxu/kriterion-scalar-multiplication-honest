import Proof.Privacy.Simulator.Arithmetic.QueryInputProtocol
import Proof.Privacy.Simulator.Arithmetic.TrialBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host supplies the query reader and chooses its return instruction. -/
def ContainsQueryInput (host : Machine) (labels : Fin 97 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 97, pc.val < 96 → host.code[(labels pc).val] =
    relocate labels (queryInput.code[pc.val]'(by exact pc.isLt))

/-- Each input block retains its source behavior inside the host. -/
theorem queryInputBlock_word (host : Machine) (labels : Fin 97 → Fin (host.size + 1))
    (present : ContainsQueryInput host labels) (width : Nat) (offset : Fin 83) (returnLabel : Fin 97)
    (source : ContainsWordInput queryInput width (queryInputLabels offset returnLabel)) :
    ContainsWordInput host width (fun pc => labels (queryInputLabels offset returnLabel pc)) := by
  intro pc inside
  have small : (queryInputLabels offset returnLabel pc).val < 96 := by
    simp only [queryInputLabels, dif_pos inside, Fin.val_mk]
    have := offset.isLt
    omega
  exact (present _ small).trans ((congrArg (relocate labels) (source pc inside)).trans
    (relocate_comp (queryInputLabels offset returnLabel) labels _))

/-- The host consumes exactly one canonical input word. -/
theorem decodedInputHost_prefix [BN254.FieldCertificate] (host : Machine) (width value : Nat)
    (labels : Fin 15 → Fin (host.size + 1))
    (present : ContainsWordInput host width labels) (base : Memory) (rest : List Bool)
    (wire : base.bits 0 = GarbledCircuit.SimulatorProtocol.bits width value ++ rest)
    (fits : width ≤ 256) :
    runPrefix host (7 * width + 6) ⟨labels 0, base⟩ =
      PMF.pure (some (false, ⟨labels 14, decodedInput base width value rest⟩, 7 * width + 6)) := by
  exact wordInputBlock_prefix host width labels present base _ rest
    (by simp [GarbledCircuit.SimulatorProtocol.bits]) wire fits

theorem queryInputBlock_tag [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 97 → Fin (host.size + 1)) (present : ContainsQueryInput host labels) (memory : Memory) :
    runPrefix host 5 ⟨labels 14, memory⟩ =
      PMF.pure (some (false,
        ⟨if (memory.registers 0).toNat < 2 then labels 19 else labels 35, queryTagState memory⟩, 5)) := by
  by_cases fixed : (memory.registers 0).toNat < 2 <;>
    simp [runPrefix, step, present 14 (by decide), present 15 (by decide), present 16 (by decide), present 17 (by decide), present 18 (by decide), relocate, queryInput, queryTagState, Arithmetic.eval, fixed, PMF.pure_map] <;> rfl


theorem queryInputBlock_family [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 97 → Fin (host.size + 1)) (present : ContainsQueryInput host labels) (memory : Memory) :
    runPrefix host 3 ⟨labels 35, memory⟩ =
      PMF.pure (some (false,
        ⟨if (memory.registers 10).toNat < 4 then labels 38 else labels 56, queryFamilyState memory⟩, 3)) := by
  by_cases enc : (memory.registers 10).toNat < 4 <;>
    simp [runPrefix, step, present 35 (by decide), present 36 (by decide), present 37 (by decide), relocate, queryInput, queryFamilyState, Arithmetic.eval, enc, PMF.pure_map] <;> rfl


theorem queryInputBlock_fixedIndex [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 97 → Fin (host.size + 1)) (present : ContainsQueryInput host labels) (memory : Memory) :
    runPrefix host 2 ⟨labels 33, memory⟩ =
      PMF.pure (some (false, ⟨labels 80, queryFixedState memory⟩, 2)) := by
  simp [runPrefix, step, present 33 (by decide), present 34 (by decide), relocate, queryInput, queryFixedState, Arithmetic.eval, PMF.pure_map]
  all_goals rfl


theorem queryInputBlock_encIndex [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 97 → Fin (host.size + 1)) (present : ContainsQueryInput host labels) (memory : Memory) :
    runPrefix host 3 ⟨labels 52, memory⟩ =
      PMF.pure (some (false, ⟨labels 80, queryEncState memory⟩, 3)) := by
  simp [runPrefix, step, present 52 (by decide), present 53 (by decide), present 54 (by decide), relocate, queryInput, queryEncState, Arithmetic.eval, PMF.pure_map]
  all_goals rfl


theorem queryInputBlock_operand [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 97 → Fin (host.size + 1)) (present : ContainsQueryInput host labels) (memory : Memory) (pc : Fin 97)
    (selected : pc = 71 ∨ pc = 94) :
    runPrefix host 1 ⟨labels pc, memory⟩ =
      PMF.pure (some (false, ⟨labels 96, queryOperandState memory⟩, 1)) := by
  rcases selected with rfl | rfl <;>
    simp [runPrefix, step, present 71 (by decide), present 94 (by decide), relocate, queryInput, queryOperandState, Arithmetic.eval, PMF.pure_map]
  all_goals rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
