import Construction.Simulator.QueryInput
import Proof.Privacy.Simulator.Arithmetic.WordInputBlock
import Proof.Privacy.Simulator.Arithmetic.WireCodec
import Proof.Privacy.Simulator.Arithmetic.MemoryLayout

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The query reader contains each fixed input block. -/
theorem queryInput_blocks :
    ContainsWordInput queryInput 3 (queryInputLabels 0 14) ∧
    ContainsWordInput queryInput 14 (queryInputLabels 19 33) ∧
    ContainsWordInput queryInput 9 (queryInputLabels 38 52) ∧
    ContainsWordInput queryInput 254 (queryInputLabels 57 71) ∧
    ContainsWordInput queryInput 128 (queryInputLabels 80 94) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro pc inside
    have guard0 : 0 + pc.val < 14 := by omega
    simp [queryInput, queryInputLabels, inside, guard0]
  · intro pc inside
    have guard0 : ¬ (19 + pc.val < 14) := by omega
    have guard1 : 19 ≤ 19 + pc.val ∧ 19 + pc.val < 33 := by omega
    simp [queryInput, queryInputLabels, inside, guard0, guard1]
  · intro pc inside
    have guard0 : ¬ (38 + pc.val < 14) := by omega
    have guard1 : ¬ (19 ≤ 38 + pc.val ∧ 38 + pc.val < 33) := by omega
    have guard2 : 38 ≤ 38 + pc.val ∧ 38 + pc.val < 52 := by omega
    simp [queryInput, queryInputLabels, inside, guard0, guard1, guard2]
  · intro pc inside
    have guard0 : ¬ (57 + pc.val < 14) := by omega
    have guard1 : ¬ (19 ≤ 57 + pc.val ∧ 57 + pc.val < 33) := by omega
    have guard2 : ¬ (38 ≤ 57 + pc.val ∧ 57 + pc.val < 52) := by omega
    have guard3 : 57 ≤ 57 + pc.val ∧ 57 + pc.val < 71 := by omega
    simp [queryInput, queryInputLabels, inside, guard0, guard1, guard2, guard3]
  · intro pc inside
    have guard0 : ¬ (80 + pc.val < 14) := by omega
    have guard1 : ¬ (19 ≤ 80 + pc.val ∧ 80 + pc.val < 33) := by omega
    have guard2 : ¬ (38 ≤ 80 + pc.val ∧ 80 + pc.val < 52) := by omega
    have guard3 : ¬ (57 ≤ 80 + pc.val ∧ 80 + pc.val < 71) := by omega
    have guard4 : 80 ≤ 80 + pc.val ∧ 80 + pc.val < 94 := by omega
    simp [queryInput, queryInputLabels, inside, guard0, guard1, guard2, guard3, guard4]

/-- The source input state retains the complete machine memory. -/
def decodedInput (base : Memory) (width value : Nat) (rest : List Bool) : Memory :=
  inputFinal base (inputFold 0 1 (base.registers 3)
    (GarbledCircuit.SimulatorProtocol.bits width value)) rest

/-- The input state exposes the canonical word and keeps the unread suffix. -/
theorem decodedInput_values (base : Memory) (width value : Nat) (rest : List Bool) :
    (decodedInput base width value rest).registers 0 = BitVec.ofNat 256 (value % 2 ^ width) ∧
    (decodedInput base width value rest).bits 0 = rest := by
  simp [decodedInput, inputFinal, inputFrame, inputFold_value, bits_value]

/-- A fixed input block consumes the canonical protocol bits. -/
theorem decodedInput_prefix [BN254.FieldCertificate] (width value : Nat)
    (labels : Fin 15 → Fin (queryInput.size + 1))
    (present : ContainsWordInput queryInput width labels) (base : Memory) (rest : List Bool)
    (wire : base.bits 0 = GarbledCircuit.SimulatorProtocol.bits width value ++ rest)
    (fits : width ≤ 256) :
    runPrefix queryInput (7 * width + 6) ⟨labels 0, base⟩ =
      PMF.pure (some (false, ⟨labels 14, decodedInput base width value rest⟩, 7 * width + 6)) := by
  exact wordInputBlock_prefix queryInput width labels present base _ rest
    (by simp [GarbledCircuit.SimulatorProtocol.bits]) wire fits

/-- The tag branch retains the tag and initializes a zero register. -/
def queryTagState (memory : Memory) : Memory :=
  { memory with
    registers := Function.update (Function.update (Function.update
      (Function.update memory.registers 15 0) 10 (memory.registers 0)) 14 2)
      6 (if (memory.registers 0).toNat < 2 then 1 else 0) }

/-- The first branch separates fixed permutations from the other query families. -/
theorem queryInput_tag [BN254.FieldCertificate] (memory : Memory) :
    runPrefix queryInput 5 ⟨14, memory⟩ =
      PMF.pure (some (false,
        ⟨if (memory.registers 0).toNat < 2 then 19 else 35, queryTagState memory⟩, 5)) := by
  by_cases fixed : (memory.registers 0).toNat < 2 <;>
    simp [runPrefix, step, queryInput, queryTagState, Arithmetic.eval, fixed, PMF.pure_map] <;> rfl

/-- The second branch distinguishes encryption permutations from the hash oracle. -/
def queryFamilyState (memory : Memory) : Memory :=
  { memory with
    registers := Function.update (Function.update memory.registers 14 4)
      6 (if (memory.registers 10).toNat < 4 then 1 else 0) }

theorem queryInput_family [BN254.FieldCertificate] (memory : Memory) :
    runPrefix queryInput 3 ⟨35, memory⟩ =
      PMF.pure (some (false,
        ⟨if (memory.registers 10).toNat < 4 then 38 else 56, queryFamilyState memory⟩, 3)) := by
  by_cases enc : (memory.registers 10).toNat < 4 <;>
    simp [runPrefix, step, queryInput, queryFamilyState, Arithmetic.eval, enc, PMF.pure_map] <;> rfl

/-- A fixed permutation retains its parsed index without an offset. -/
def queryFixedState (memory : Memory) : Memory :=
  { memory with
    registers := Function.update
      (Function.update memory.registers 9 (memory.registers 0 + memory.registers 15)) 15 0 }

theorem queryInput_fixedIndex [BN254.FieldCertificate] (memory : Memory) :
    runPrefix queryInput 2 ⟨33, memory⟩ =
      PMF.pure (some (false, ⟨80, queryFixedState memory⟩, 2)) := by
  simp [runPrefix, step, queryInput, queryFixedState, Arithmetic.eval, PMF.pure_map]
  all_goals rfl

/-- An encryption permutation follows all shared fixed-key permutations. -/
def queryEncState (memory : Memory) : Memory :=
  { memory with
    registers := Function.update (Function.update
      (Function.update memory.registers 14 15240) 9 (memory.registers 0 + 15240)) 15 0 }

theorem queryInput_encIndex [BN254.FieldCertificate] (memory : Memory) :
    runPrefix queryInput 3 ⟨52, memory⟩ =
      PMF.pure (some (false, ⟨80, queryEncState memory⟩, 3)) := by
  simp [runPrefix, step, queryInput, queryEncState, Arithmetic.eval, PMF.pure_map]
  all_goals rfl

/-- The output move retains the parsed operand in register eight. -/
def queryOperandState (memory : Memory) : Memory :=
  { memory with
    registers := Function.update memory.registers 8
      (memory.registers 0 + memory.registers 15) }

theorem queryInput_operand [BN254.FieldCertificate] (memory : Memory) (pc : Fin 97)
    (selected : pc = 71 ∨ pc = 94) :
    runPrefix queryInput 1 ⟨pc, memory⟩ =
      PMF.pure (some (false, ⟨96, queryOperandState memory⟩, 1)) := by
  rcases selected with rfl | rfl <;>
    simp [runPrefix, step, queryInput, queryOperandState, Arithmetic.eval, PMF.pure_map]
  all_goals rfl

/-- The input word retains a value that fits the selected width. -/
theorem decodedInput_value (base : Memory) (width value : Nat) (rest : List Bool)
    (fits : value < 2 ^ width) :
    (decodedInput base width value rest).registers 0 = BitVec.ofNat 256 value := by
  rw [(decodedInput_values base width value rest).1, Nat.mod_eq_of_lt fits]

end Kriterion.ArgoMAC.ArithmeticSimulator
