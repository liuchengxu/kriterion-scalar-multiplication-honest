import Construction.Simulator.WideSampler
import Proof.Privacy.Simulator.Arithmetic.WordBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
set_option exponentiation.threshold 257

/-- The larger program contains all twelve sampler instructions. -/
theorem wideSampler_contains (width : Nat) (extra : Bool) :
    ContainsWordSampler (wideSampler width extra) width wideLabels := by
  intro pc inside
  simp [wideSampler, wideLabels, inside]

/-- This frame stores the low word and the extra bit. -/
def wideFrame (base : Memory) (value : Word) (bit : Bool) : Memory :=
  {frame base value 0 0 with
    registers := Function.update (frame base value 0 0).registers 6 (if bit then 1 else 0)}

/-- The final block draws one extra fair bit and restores its stack. -/
theorem wideSampler_tail [BN254.FieldCertificate] (width : Nat) (base : Memory) :
    run (wideSampler width true) 4 ⟨12, base⟩ =
      (PMF.uniformOfFintype Bool).map fun bit =>
        some (⟨16, {base with registers := Function.update base.registers 6 (if bit then 1 else 0)}⟩, 4) := by
  simp [run, step, wideSampler, Function.update, PMF.map_bind, PMF.bind_bind]
  congr 1
  funext bit
  cases bit <;> simp [PMF.pure_map] <;> rfl

/-- The wide sampler returns independent low bits and one high bit. -/
theorem wideSampler_run [BN254.FieldCertificate] (width : Nat) (base : Memory)
    (fits : width ≤ 256) :
    run (wideSampler width true) (7 * width + 9) ⟨0, base⟩ =
      (coinFold width 0).bind fun output =>
        (PMF.uniformOfFintype Bool).map fun bit =>
          some (⟨16, wideFrame base output bit⟩, 7 * width + 9) := by
  rw [show 7 * width + 9 = (7 * width + 5) + 4 by omega, run_after_prefix]
  change (runPrefix (wideSampler width true) (7 * width + 5)
    ⟨wideLabels 0, base⟩).bind _ = _
  erw [wordBlock_prefix (wideSampler width true) width wideLabels (wideSampler_contains width true) base fits]
  simp only [PMF.bind_map, Function.comp_def]
  change (coinFold width 0).bind (fun output =>
    (run (wideSampler width true) 4 ⟨12, frame base output 0 0⟩).map _) = _
  simp only [wideSampler_tail, PMF.map_comp, Function.comp_def, Option.map_some]
  simp only [wideFrame, Nat.add_comm]

/-- The 257-bit sampler uses exactly 1801 instructions. -/
theorem wideSampler_257 [BN254.FieldCertificate] (base : Memory) :
    run (wideSampler 256 true) 1801 ⟨0, base⟩ =
      (PMF.uniformOfFintype Word).bind fun output =>
        (PMF.uniformOfFintype Bool).map fun bit =>
          some (⟨16, wideFrame base output bit⟩, 1801) := by
  rw [show 1801 = 7 * 256 + 9 from rfl, wideSampler_run 256 base (by decide),
    coinFold_word_uniform]

/-- The narrow path clears the unused high bit and retains the same low-bit law. -/
theorem wideSampler_narrow [BN254.FieldCertificate] (width : Nat) (base : Memory)
    (fits : width ≤ 256) :
    run (wideSampler width false) (7 * width + 7) ⟨0, base⟩ =
      (coinFold width 0).map fun output =>
        some (⟨16, wideFrame base output false⟩, 7 * width + 7) := by
  rw [show 7 * width + 7 = (7 * width + 5) + 2 by omega, run_after_prefix]
  change (runPrefix (wideSampler width false) (7 * width + 5)
    ⟨wideLabels 0, base⟩).bind _ = _
  erw [wordBlock_prefix (wideSampler width false) width wideLabels
    (wideSampler_contains width false) base fits]
  simp only [PMF.bind_map, Function.comp_def]
  simp [run, step, wideSampler, wideLabels, PMF.pure_map, wideFrame, Nat.add_comm]
  rfl

/-- This equivalence retains all 257 bits across two registers. -/
def widePair : Word × Bool ≃ Fin (2 ^ 257) :=
  (Equiv.prodComm Word Bool).trans
    ((Equiv.prodCongr (Equiv.refl Bool) BitVec.equivFin.toEquiv).trans (bitPair 256))

/-- The high bit contributes exactly one word range. -/
theorem widePair_value (value : Word) (bit : Bool) :
    (widePair (value, bit)).val = value.toNat + 2 ^ 256 * (if bit then 1 else 0) := by
  cases bit <;> simp [widePair, bitPair, finProdFinEquiv, finTwoEquiv, BitVec.equivFin]

/-- This observer reads the low word and the separate high bit. -/
def wideValue (memory : Memory) : Fin (2 ^ 257) :=
  widePair (memory.registers 0, decide (memory.registers 6 ≠ 0))

/-- The observer retains each sampled bit. -/
theorem wideValue_frame (base : Memory) (value : Word) (bit : Bool) :
    wideValue (wideFrame base value bit) = widePair (value, bit) := by
  cases bit <;> simp [wideValue, wideFrame, frame]

/-- The actual machine returns each 257-bit integer with equal probability. -/
theorem wideSampler_257_uniform [BN254.FieldCertificate] (base : Memory) :
    (run (wideSampler 256 true) 1801 ⟨0, base⟩).map
      (Option.map fun result => (wideValue result.1.memory, result.2)) =
        (PMF.uniformOfFintype (Fin (2 ^ 257))).map fun value => some (value, 1801) := by
  rw [wideSampler_257, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, Option.map_some, wideValue_frame]
  change ((PMF.uniformOfFintype Word).bind fun output =>
    (PMF.uniformOfFintype Bool).bind fun bit => PMF.pure (some (widePair (output, bit), 1801))) = _
  rw [← Security.uniform_product_bind (fun pair : Word × Bool =>
    PMF.pure (some (widePair pair, 1801)))]
  rw [← Security.uniform_map_equiv widePair, PMF.map_comp]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
