import Construction.Simulator.WordInput
import Proof.Privacy.Simulator.Arithmetic.Blocks
import Security.AdaptivePrivacy

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

def inputFrame (base : Memory) (value weight : Word) (count : Nat)
    (temporary : Word) (source : List Bool) : Memory :=
  { base with
    bits := Function.update base.bits 0 source
    registers := Function.update (Function.update (Function.update
      (Function.update (Function.update base.registers 4 1) 3 temporary)
        2 (BitVec.ofNat 256 count)) 1 weight) 0 value }

theorem inputCount_ne_zero (count : Nat) (fits : count + 1 ≤ 256) :
    BitVec.ofNat 256 (count + 1) ≠ 0#256 := by
  intro equal
  have small : count + 1 < 2 ^ 256 := lt_of_le_of_lt fits (by decide)
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at natural
  change count + 1 = 0 at natural
  omega

/-- The input loop consumes one bit in seven instructions. -/
theorem wordInput_step [BN254.FieldCertificate] (width count fuel : Nat)
    (base : Memory) (value weight temporary : Word) (bit : Bool) (rest : List Bool)
    (fits : count + 1 ≤ 256) :
    runPrefix (wordInput width) (fuel + 7)
      ⟨4, inputFrame base value weight (count + 1) temporary (bit :: rest)⟩ =
      (runPrefix (wordInput width) fuel
        ⟨4, inputFrame base (value + if bit then weight else 0) (weight + weight)
          count (if bit then weight else 0) rest⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 7)) := by
  have countStep : BitVec.ofNat 256 (count + 1) - 1#256 = BitVec.ofNat 256 count := by
    rw [BitVec.ofNat_add]
    simp
  cases bit <;>
    simp [runPrefix, step, wordInput, inputFrame, Arithmetic.eval,
      inputCount_ne_zero count fits, countStep, Function.update, Function.update_comm,
      PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc] <;> rfl

/-- This fold records the value, weight, and temporary word after the input bits. -/
def inputFold (value weight temporary : Word) : List Bool → Word × Word × Word
  | [] => (value, weight, temporary)
  | bit :: rest => inputFold (value + if bit then weight else 0) (weight + weight)
      (if bit then weight else 0) rest

def inputFinal (base : Memory) (result : Word × Word × Word) (rest : List Bool) : Memory :=
  let memory := inputFrame base result.1 result.2.1 0 result.2.2 rest
  { memory with registers := Function.update memory.registers 7 1 }

/-- The input loop retains the suffix after the requested bits. -/
theorem wordInput_loop [BN254.FieldCertificate] (width : Nat)
    (base : Memory) (value weight temporary : Word) (source rest : List Bool)
    (fits : source.length ≤ 256) :
    runPrefix (wordInput width) (7 * source.length + 2)
      ⟨4, inputFrame base value weight source.length temporary (source ++ rest)⟩ =
      PMF.pure (some (false, ⟨14, inputFinal base (inputFold value weight temporary source) rest⟩,
        7 * source.length + 2)) := by
  induction source generalizing value weight temporary with
  | nil => simp [runPrefix, step, wordInput, inputFold, inputFinal, inputFrame, PMF.pure_map]; rfl
  | cons bit source ih =>
      rw [List.length_cons, List.cons_append,
        show 7 * (source.length + 1) + 2 = (7 * source.length + 2) + 7 by omega,
        wordInput_step width source.length (7 * source.length + 2) base value weight temporary
          bit (source ++ rest) (by simpa using fits), ih _ _ _ (by simpa using Nat.le_of_succ_le fits)]
      simp [inputFold, PMF.pure_map, Nat.add_assoc]

/-- The entry initializes the input loop in four instructions. -/
theorem wordInput_setup [BN254.FieldCertificate] (width fuel : Nat) (base : Memory) :
    runPrefix (wordInput width) (fuel + 4) ⟨0, base⟩ =
      (runPrefix (wordInput width) fuel
        ⟨4, inputFrame base 0 1 width (base.registers 3) (base.bits 0)⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 4)) := by
  simp [runPrefix, step, wordInput, inputFrame, Function.update_comm,
    Function.update_eq_self, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]
  rfl

/-- The full input prefix consumes the requested bits and sets the success flag. -/
theorem wordInput_prefix [BN254.FieldCertificate] (width : Nat)
    (base : Memory) (source rest : List Bool) (length : source.length = width)
    (wire : base.bits 0 = source ++ rest) (fits : width ≤ 256) :
    runPrefix (wordInput width) (7 * width + 6) ⟨0, base⟩ =
      PMF.pure (some (false, ⟨14,
        inputFinal base (inputFold 0 1 (base.registers 3) source) rest⟩, 7 * width + 6)) := by
  rw [show 7 * width + 6 = (7 * width + 2) + 4 by omega,
    wordInput_setup, wire, ← length,
    wordInput_loop source.length base 0 1 (base.registers 3) source rest (by omega)]
  simp [PMF.pure_map]

/-- The machine returns the input value and retains its exact instruction cost. -/
theorem wordInput_run [BN254.FieldCertificate] (width : Nat)
    (base : Memory) (source rest : List Bool) (length : source.length = width)
    (wire : base.bits 0 = source ++ rest) (fits : width ≤ 256) :
    run (wordInput width) (7 * width + 7) ⟨0, base⟩ =
      PMF.pure (some (⟨14,
        inputFinal base (inputFold 0 1 (base.registers 3) source) rest⟩, 7 * width + 7)) := by
  rw [show 7 * width + 7 = (7 * width + 6) + 1 by omega,
    run_after_prefix, wordInput_prefix width base source rest length wire fits, PMF.pure_bind]
  simp [run, step, wordInput, PMF.pure_map, Nat.add_comm]

/-- The input fold computes the same little-endian value as the protocol parser. -/
theorem inputFold_value (value weight temporary : Word) (source : List Bool) :
    (inputFold value weight temporary source).1 = value + weight * BitVec.ofNat 256
      (source.foldr (fun bit acc => bit.toNat + 2 * acc) 0) := by
  induction source generalizing value weight temporary with
  | nil => simp [inputFold]
  | cons bit source ih =>
      simp only [inputFold, List.foldr_cons, ih]
      cases bit <;> simp [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.mul_add,
        BitVec.add_mul, BitVec.two_mul, BitVec.add_assoc]

/-- The machine result uses the protocol parser's little-endian fold. -/
theorem wordInput_source [BN254.FieldCertificate] (width : Nat)
    (base : Memory) (source rest : List Bool) (length : source.length = width)
    (wire : base.bits 0 = source ++ rest) (fits : width ≤ 256) :
    (run (wordInput width) (7 * width + 7) ⟨0, base⟩).map
      (Option.map fun result => (result.1.memory.registers 0,
        result.1.memory.registers 7, result.1.memory.bits 0, result.2)) =
      PMF.pure (some (BitVec.ofNat 256
        (source.foldr (fun bit acc => bit.toNat + 2 * acc) 0), 1, rest, 7 * width + 7)) := by
  rw [wordInput_run width base source rest length wire fits, PMF.pure_map]
  simp [inputFinal, inputFrame, inputFold_value]

/-- The reader leaves every RAM word unchanged. -/
theorem inputFinal_ram (base : Memory) (result : Word × Word × Word) (rest : List Bool) :
    (inputFinal base result rest).ram = base.ram := rfl

/-- A caller retains registers eight through fifteen after the input block. -/
theorem inputFinal_caller (base : Memory) (result : Word × Word × Word) (rest : List Bool)
    (register : Register) (saved : 8 ≤ register.val) :
    (inputFinal base result rest).registers register = base.registers register := by
  have different (target : Register) (small : target.val < 8) : register ≠ target := by
    intro equal
    have values := congrArg Fin.val equal
    omega
  simp only [inputFinal, inputFrame]
  rw [Function.update_of_ne (different 7 (by decide)),
    Function.update_of_ne (different 0 (by decide)),
    Function.update_of_ne (different 1 (by decide)),
    Function.update_of_ne (different 2 (by decide)),
    Function.update_of_ne (different 3 (by decide)),
    Function.update_of_ne (different 4 (by decide))]

/-- The input budget includes all 15 entries in the program table. -/
theorem wordInput_budget (width : Nat) (fits : width ≤ 256) :
    (wordInput width).size + 1 + (7 * width + 7) ≤ 1814 := by
  change 14 + 1 + (7 * width + 7) ≤ 1814
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
