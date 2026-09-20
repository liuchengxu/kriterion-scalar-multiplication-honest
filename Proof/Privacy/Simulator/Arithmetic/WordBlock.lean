import Construction.Simulator.Assembly
import Proof.Privacy.Simulator.Arithmetic.Blocks
import Proof.Privacy.Simulator.Arithmetic.WordSampler

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A host program contains the twelve sampler instructions before the return label. -/
def ContainsWordSampler (host : Machine) (width : Nat)
    (labels : Fin 13 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 13, pc.val < 12 → host.code[(labels pc).val] =
    relocate labels ((wordSampler width).code[pc.val]'(by change pc.val < 13; exact pc.isLt))

/-- A host contains the loop instructions without fixing the initial bit count. -/
def ContainsWordLoop (host : Machine) (labels : Fin 13 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 13, 3 ≤ pc.val → pc.val < 12 → host.code[(labels pc).val] =
    relocate labels ((wordSampler 0).code[pc.val]'(by change pc.val < 13; exact pc.isLt))

/-- The complete sampler contains the same loop for every initial bit count. -/
theorem ContainsWordSampler.loop (host : Machine) (width : Nat)
    (labels : Fin 13 → Fin (host.size + 1)) (present : ContainsWordSampler host width labels) :
    ContainsWordLoop host labels := by
  intro pc lower upper
  have selected := present pc upper
  have same : (wordSampler width).code[pc.val] = (wordSampler 0).code[pc.val] := by
    fin_cases pc <;> simp_all [wordSampler]
  exact selected.trans (congrArg (relocate labels) same)

private theorem count_ne_zero (count : Nat) (fits : count + 1 ≤ 256) :
    BitVec.ofNat 256 (count + 1) ≠ 0#256 := by
  intro equal
  have small : count + 1 < 2 ^ 256 := lt_of_le_of_lt fits (by decide)
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at natural
  change count + 1 = 0 at natural
  omega

/-- The host executes one sampling loop in seven instructions. -/
theorem wordBlock_step [BN254.FieldCertificate] (host : Machine) (count fuel : Nat)
    (labels : Fin 13 → Fin (host.size + 1)) (present : ContainsWordLoop host labels)
    (base : Memory) (value bit : Word) (fits : count + 1 ≤ 256) :
    runPrefix host (fuel + 7) ⟨labels 3, frame base value (count + 1) bit⟩ =
      (PMF.uniformOfFintype Bool).bind fun sampled =>
        (runPrefix host fuel
          ⟨labels 3, frame base (value + value + if sampled then 1 else 0) count
            (if sampled then 1 else 0)⟩).map
          (Option.map fun result => (result.1, result.2.1, result.2.2 + 7)) := by
  have countStep : BitVec.ofNat 256 (count + 1) - 1#256 = BitVec.ofNat 256 count := by
    rw [BitVec.ofNat_add]
    simp
  simp [runPrefix, step, present 3 (by decide) (by decide), present 4 (by decide) (by decide), present 5 (by decide) (by decide), present 6 (by decide) (by decide), present 7 (by decide) (by decide),
    present 8 (by decide) (by decide), present 9 (by decide) (by decide), present 10 (by decide) (by decide), wordSampler, relocate, frame, Arithmetic.eval,
    count_ne_zero count fits, Function.update, PMF.map_bind, PMF.map_comp,
    PMF.bind_bind, Function.comp_def]
  congr 1
  funext sampled
  cases sampled <;> simp [present 6 (by decide) (by decide), present 7 (by decide) (by decide), present 8 (by decide) (by decide), present 9 (by decide) (by decide), present 10 (by decide) (by decide),
    wordSampler, relocate, Arithmetic.eval, Function.update, countStep,
    PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc, Function.update_comm]

/-- The sampler returns control before it executes the host's continuation. -/
theorem wordBlock_loop [BN254.FieldCertificate] (host : Machine) (count : Nat)
    (labels : Fin 13 → Fin (host.size + 1)) (present : ContainsWordLoop host labels)
    (base : Memory) (value bit : Word) (fits : count ≤ 256) :
    runPrefix host (7 * count + 2) ⟨labels 3, frame base value count bit⟩ =
      (coinFold count value).map fun output =>
        some (false, ⟨labels 12, frame base output 0 0⟩, 7 * count + 2) := by
  induction count generalizing value bit with
  | zero =>
      simp [coinFold, runPrefix, step, present 3 (by decide) (by decide), present 11 (by decide) (by decide), wordSampler, relocate,
        frame, Function.update_comm, PMF.pure_map]
  | succ count ih =>
      rw [show 7 * (count + 1) + 2 = (7 * count + 2) + 7 by omega,
        wordBlock_step host count (7 * count + 2) labels present base value bit fits,
        coinFold, PMF.map_bind]
      congr 1
      funext sampled
      rw [ih _ _ (by omega)]
      simp [PMF.map_comp, Function.comp_def, Nat.mul_succ, Nat.add_assoc]

/-- The host initializes the sampler in three instructions. -/
theorem wordBlock_setup [BN254.FieldCertificate] (host : Machine) (width fuel : Nat)
    (labels : Fin 13 → Fin (host.size + 1)) (present : ContainsWordSampler host width labels)
    (base : Memory) :
    runPrefix host (fuel + 3) ⟨labels 0, base⟩ =
      (runPrefix host fuel ⟨labels 3, frame base 0 width (base.registers 3)⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 3)) := by
  simp [runPrefix, step, present 0 (by decide), present 1 (by decide), present 2 (by decide), wordSampler, relocate, frame,
    Function.update_comm, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The embedded block has the same fair-bit law as the standalone sampler. -/
theorem wordBlock_prefix [BN254.FieldCertificate] (host : Machine) (width : Nat)
    (labels : Fin 13 → Fin (host.size + 1)) (present : ContainsWordSampler host width labels)
    (base : Memory) (fits : width ≤ 256) :
    runPrefix host (7 * width + 5) ⟨labels 0, base⟩ =
      (coinFold width 0).map fun output =>
        some (false, ⟨labels 12, frame base output 0 0⟩, 7 * width + 5) := by
  rw [show 7 * width + 5 = (7 * width + 2) + 3 by omega,
    wordBlock_setup host width (7 * width + 2) labels present base,
    wordBlock_loop host width labels (ContainsWordSampler.loop host width labels present) base 0 (base.registers 3) fits]
  simp [PMF.map_comp, Function.comp_def, Nat.add_assoc]

/-- The host resumes after a uniform draw and retains the 1797-instruction prefix cost. -/
theorem wordBlock_continue [BN254.FieldCertificate] (host : Machine) (fuel : Nat)
    (labels : Fin 13 → Fin (host.size + 1)) (present : ContainsWordSampler host 256 labels)
    (base : Memory) :
    run host (1797 + fuel) ⟨labels 0, base⟩ =
      (PMF.uniformOfFintype Word).bind fun output =>
        (run host fuel ⟨labels 12, frame base output 0 0⟩).map
          (Option.map fun result => (result.1, result.2 + 1797)) := by
  rw [run_after_prefix, show 1797 = 7 * 256 + 5 from rfl,
    wordBlock_prefix host 256 labels present base (by decide), coinFold_word_uniform]
  simp only [PMF.bind_map, Function.comp_def]

end Kriterion.ArgoMAC.ArithmeticSimulator
