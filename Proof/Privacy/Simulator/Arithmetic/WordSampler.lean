import Construction.Simulator.WordSampler
import Proof.Privacy.Distribution.PublicDistribution

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- This frame records the four sampler registers and preserves all other memory. -/
def frame (base : Memory) (value : Word) (remaining : Nat) (bit : Word) : Memory :=
  {base with registers := Function.update (Function.update (Function.update
    (Function.update base.registers 3 bit) 2 (BitVec.ofNat 256 remaining)) 1 1) 0 value}

/-- This law uses one independent fair bit for each loop. -/
noncomputable def coinFold : Nat → Word → PMF Word
  | 0, value => PMF.pure value
  | count + 1, value => (PMF.uniformOfFintype Bool).bind fun bit =>
      coinFold count (value + value + if bit then 1 else 0)

private theorem count_nonzero (count : Nat) (fits : count + 1 ≤ 256) :
    BitVec.ofNat 256 (count + 1) ≠ 0#256 := by
  intro equal
  have small : count + 1 < 2 ^ 256 := lt_of_le_of_lt fits (by decide)
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at natural
  change count + 1 = 0 at natural
  omega

/-- Each loop uses seven instructions and restores the random-bit stack. -/
theorem loop_step [BN254.FieldCertificate] (width count fuel : Nat)
    (base : Memory) (value bit : Word) (fits : count + 1 ≤ 256) :
    run (wordSampler width) (fuel + 7) ⟨3, frame base value (count + 1) bit⟩ =
      (PMF.uniformOfFintype Bool).bind fun sampled =>
        (run (wordSampler width) fuel
          ⟨3, frame base (value + value + if sampled then 1 else 0) count
            (if sampled then 1 else 0)⟩).map
          (Option.map fun result => (result.1, result.2 + 7)) := by
  have countStep : BitVec.ofNat 256 (count + 1) - 1#256 = BitVec.ofNat 256 count := by
    rw [BitVec.ofNat_add]
    simp
  simp [run, step, wordSampler, frame, Arithmetic.eval, count_nonzero count fits,
    Function.update, PMF.map_bind, PMF.map_comp, PMF.bind_bind, Function.comp_def]
  congr 1
  funext sampled
  cases sampled <;> simp [Arithmetic.eval, Function.update, countStep,
    PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc,
    Function.update_comm]
  all_goals rfl

/-- The loop has the exact fair-bit law and an exact instruction count. -/
theorem loop_run [BN254.FieldCertificate] (width count : Nat)
    (base : Memory) (value bit : Word) (fits : count ≤ 256) :
    run (wordSampler width) (7 * count + 3) ⟨3, frame base value count bit⟩ =
      (coinFold count value).map fun output =>
        some (⟨12, frame base output 0 0⟩, 7 * count + 3) := by
  induction count generalizing value bit with
  | zero =>
      simp [coinFold, run, step, wordSampler, frame, Function.update_comm, PMF.pure_map] <;> rfl
  | succ count ih =>
      rw [show 7 * (count + 1) + 3 = (7 * count + 3) + 7 by omega,
        loop_step width count (7 * count + 3) base value bit fits, coinFold, PMF.map_bind]
      congr 1
      funext sampled
      rw [ih _ _ (by omega)]
      simp [PMF.map_comp, Function.comp_def, Nat.mul_succ, Nat.add_assoc]

/-- The initial three instructions set the value, one, and the bit count. -/
theorem setup_run [BN254.FieldCertificate] (width fuel : Nat) (base : Memory) :
    run (wordSampler width) (fuel + 3) ⟨0, base⟩ =
      (run (wordSampler width) fuel ⟨3, frame base 0 width (base.registers 3)⟩).map
        (Option.map fun result => (result.1, result.2 + 3)) := by
  simp [run, step, wordSampler, frame, Function.update_comm, PMF.map_comp,
    Option.map_map, Function.comp_def, Nat.add_assoc]
  rfl

/-- The closed sampler uses seven instructions per bit and six fixed instructions. -/
theorem wordSampler_run [BN254.FieldCertificate] (width : Nat) (base : Memory)
    (fits : width ≤ 256) :
    run (wordSampler width) (7 * width + 6) ⟨0, base⟩ =
      (coinFold width 0).map fun output =>
        some (⟨12, frame base output 0 0⟩, 7 * width + 6) := by
  rw [show 7 * width + 6 = (7 * width + 3) + 3 by omega,
    setup_run, loop_run width width base 0 (base.registers 3) fits]
  simp [PMF.map_comp, Function.comp_def, Nat.add_assoc]

/-- This equivalence joins one leading bit and the remaining lower bits. -/
def bitPair (count : Nat) : Bool × Fin (2 ^ count) ≃ Fin (2 ^ (count + 1)) :=
  (Equiv.prodCongr finTwoEquiv.symm (Equiv.refl _)).trans
    (finProdFinEquiv.trans (finCongr (by simp [pow_succ, Nat.mul_comm])))

private theorem bitPair_value (count : Nat) (bit : Bool) (tail : Fin (2 ^ count)) :
    (bitPair count (bit, tail)).val = tail.val + 2 ^ count * (if bit then 1 else 0) := by
  cases bit <;> simp [bitPair, finProdFinEquiv, finTwoEquiv]

/-- Independent fair bits give the exact uniform integer law before word reduction. -/
theorem coinFold_uniform (count : Nat) (value : Word) :
    coinFold count value = (PMF.uniformOfFintype (Fin (2 ^ count))).map
      (fun sample => value * BitVec.ofNat 256 (2 ^ count) + BitVec.ofNat 256 sample.val) := by
  induction count generalizing value with
  | zero =>
      simp [coinFold]
      exact (PMF.map_const (PMF.uniformOfFintype (Fin 1)) value).symm
  | succ count ih =>
      simp only [coinFold, ih]
      change ((PMF.uniformOfFintype Bool).bind fun bit =>
        (PMF.uniformOfFintype (Fin (2 ^ count))).bind fun tail =>
          PMF.pure ((value + value + if bit then 1 else 0) * BitVec.ofNat 256 (2 ^ count) +
            BitVec.ofNat 256 tail.val)) = _
      rw [← Security.uniform_product_bind (fun pair : Bool × Fin (2 ^ count) =>
        PMF.pure ((value + value + if pair.1 then 1 else 0) * BitVec.ofNat 256 (2 ^ count) +
          BitVec.ofNat 256 pair.2.val))]
      rw [← Security.uniform_map_equiv (bitPair count), PMF.map_comp]
      change (PMF.uniformOfFintype (Bool × Fin (2 ^ count))).map _ = _
      congr 1
      funext pair
      rcases pair with ⟨bit, tail⟩
      simp only [Function.comp_def, bitPair_value, pow_succ, BitVec.ofNat_add, BitVec.ofNat_mul]
      cases bit <;> simp
      all_goals simp only [show (1#256 : Word) = 1 from rfl,
        show (2#256 : Word) = 2 from rfl]
      all_goals ring

/-- The 256-bit sampler returns each machine word with the same probability. -/
theorem coinFold_word_uniform : coinFold 256 0 = PMF.uniformOfFintype Word := by
  rw [coinFold_uniform]
  simpa [BitVec.equivFin] using Security.uniform_map_equiv
    (BitVec.equivFin.toEquiv.symm : Fin (2 ^ 256) ≃ Word)

/-- The actual machine returns a uniform word in exactly 1798 instructions. -/
theorem wordSampler_uniform [BN254.FieldCertificate] (base : Memory) :
    run (wordSampler 256) 1798 ⟨0, base⟩ =
      (PMF.uniformOfFintype Word).map fun output =>
        some (⟨12, frame base output 0 0⟩, 1798) := by
  rw [show 1798 = 7 * 256 + 6 from rfl, wordSampler_run 256 base (by decide), coinFold_word_uniform]

end Kriterion.ArgoMAC.ArithmeticSimulator
