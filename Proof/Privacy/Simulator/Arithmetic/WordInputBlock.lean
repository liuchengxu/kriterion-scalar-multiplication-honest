import Construction.Simulator.Assembly
import Proof.Privacy.Simulator.Arithmetic.WordInput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host supplies the input instructions and chooses its own return instruction. -/
def ContainsWordInput (host : Machine) (width : Nat)
    (labels : Fin 15 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 15, pc.val < 14 → host.code[(labels pc).val] =
    relocate labels ((wordInput width).code[pc.val]'(by change pc.val < 15; exact pc.isLt))

/-- The host consumes one input bit in seven instructions. -/
theorem wordInputBlock_step [BN254.FieldCertificate] (host : Machine)
    (width count fuel : Nat) (labels : Fin 15 → Fin (host.size + 1))
    (present : ContainsWordInput host width labels)
    (base : Memory) (value weight temporary : Word) (bit : Bool) (rest : List Bool)
    (fits : count + 1 ≤ 256) :
    runPrefix host (fuel + 7)
      ⟨labels 4, inputFrame base value weight (count + 1) temporary (bit :: rest)⟩ =
      (runPrefix host fuel
        ⟨labels 4, inputFrame base (value + if bit then weight else 0) (weight + weight)
          count (if bit then weight else 0) rest⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 7)) := by
  have countStep : BitVec.ofNat 256 (count + 1) - 1#256 = BitVec.ofNat 256 count := by
    rw [BitVec.ofNat_add]
    simp
  cases bit <;>
    simp [runPrefix, step, present 4 (by decide), present 5 (by decide),
      present 6 (by decide), present 7 (by decide), present 8 (by decide),
      present 9 (by decide), present 10 (by decide), present 12 (by decide),
      wordInput, relocate, inputFrame, Arithmetic.eval,
      inputCount_ne_zero count fits, countStep, Function.update, Function.update_comm,
      PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc] <;> rfl

/-- The input loop returns before the host executes its continuation. -/
theorem wordInputBlock_loop [BN254.FieldCertificate] (host : Machine)
    (width : Nat) (labels : Fin 15 → Fin (host.size + 1))
    (present : ContainsWordInput host width labels)
    (base : Memory) (value weight temporary : Word) (source rest : List Bool)
    (fits : source.length ≤ 256) :
    runPrefix host (7 * source.length + 2)
      ⟨labels 4, inputFrame base value weight source.length temporary (source ++ rest)⟩ =
      PMF.pure (some (false, ⟨labels 14,
        inputFinal base (inputFold value weight temporary source) rest⟩,
        7 * source.length + 2)) := by
  induction source generalizing value weight temporary with
  | nil =>
      simp [runPrefix, step, present 4 (by decide), present 11 (by decide),
        wordInput, relocate, inputFold, inputFinal, inputFrame, PMF.pure_map]
  | cons bit source ih =>
      rw [List.length_cons, List.cons_append,
        show 7 * (source.length + 1) + 2 = (7 * source.length + 2) + 7 by omega,
        wordInputBlock_step host width source.length (7 * source.length + 2) labels present
          base value weight temporary bit (source ++ rest) (by simpa using fits),
        ih _ _ _ (by simpa using Nat.le_of_succ_le fits)]
      simp [inputFold, PMF.pure_map, Nat.add_assoc]

/-- The host initializes the input registers in four instructions. -/
theorem wordInputBlock_setup [BN254.FieldCertificate] (host : Machine)
    (width fuel : Nat) (labels : Fin 15 → Fin (host.size + 1))
    (present : ContainsWordInput host width labels) (base : Memory) :
    runPrefix host (fuel + 4) ⟨labels 0, base⟩ =
      (runPrefix host fuel
        ⟨labels 4, inputFrame base 0 1 width (base.registers 3) (base.bits 0)⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 4)) := by
  simp [runPrefix, step, present 0 (by decide), present 1 (by decide),
    present 2 (by decide), present 3 (by decide), wordInput, relocate, inputFrame,
    Function.update_comm, Function.update_eq_self, PMF.map_comp,
    Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The input prefix retains the caller memory and the unread suffix. -/
theorem wordInputBlock_prefix [BN254.FieldCertificate] (host : Machine)
    (width : Nat) (labels : Fin 15 → Fin (host.size + 1))
    (present : ContainsWordInput host width labels)
    (base : Memory) (source rest : List Bool) (length : source.length = width)
    (wire : base.bits 0 = source ++ rest) (fits : width ≤ 256) :
    runPrefix host (7 * width + 6) ⟨labels 0, base⟩ =
      PMF.pure (some (false, ⟨labels 14,
        inputFinal base (inputFold 0 1 (base.registers 3) source) rest⟩, 7 * width + 6)) := by
  have loop := wordInputBlock_loop host width labels present base 0 1 (base.registers 3)
    source rest (by omega)
  rw [length] at loop
  rw [show 7 * width + 6 = (7 * width + 2) + 4 by omega,
    wordInputBlock_setup host width (7 * width + 2) labels present base, wire, loop]
  simp [PMF.pure_map]

/-- The caller resumes with the exact input prefix cost. -/
theorem wordInputBlock_continue [BN254.FieldCertificate] (host : Machine)
    (width fuel : Nat) (labels : Fin 15 → Fin (host.size + 1))
    (present : ContainsWordInput host width labels)
    (base : Memory) (source rest : List Bool) (length : source.length = width)
    (wire : base.bits 0 = source ++ rest) (fits : width ≤ 256) :
    run host (7 * width + 6 + fuel) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels 14,
        inputFinal base (inputFold 0 1 (base.registers 3) source) rest⟩).map
        (Option.map fun result => (result.1, result.2 + (7 * width + 6))) := by
  rw [run_after_prefix, wordInputBlock_prefix host width labels present base source rest
    length wire fits, PMF.pure_bind]

end Kriterion.ArgoMAC.ArithmeticSimulator
