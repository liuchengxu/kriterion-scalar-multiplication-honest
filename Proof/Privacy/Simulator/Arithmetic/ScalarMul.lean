import Construction.Simulator.ScalarMul
import Proof.Privacy.Simulator.Arithmetic.PointMemory
import Proof.Privacy.Simulator.Arithmetic.RangeWidth

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A one-bit mask gives the scalar remainder modulo two. -/
theorem scalar_lowBit (value : Nat) (fits : value < 2 ^ 256) :
    BitVec.ofNat 256 value &&& 1#256 = BitVec.ofNat 256 (value % 2) := by
  apply BitVec.eq_of_toNat_eq
  have small : value % 2 < 2 ^ 256 := lt_trans (Nat.mod_lt value (by decide)) (by decide)
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits, Nat.mod_eq_of_lt small]
  exact Nat.and_one_is_mod value

/-- The accumulator uses three distinct registers. -/
theorem scalarAccumulator_write [BN254.FieldCertificate] (registers : Register → Word) (point : BN254.Point) :
    readPoint (writePoint registers scalarAccumulator point) scalarAccumulator = some point :=
  readPoint_writePoint registers scalarAccumulator point (by decide) (by decide) (by decide)

/-- The current multiple uses three distinct registers. -/
theorem scalarMultiple_write [BN254.FieldCertificate] (registers : Register → Word) (point : BN254.Point) :
    readPoint (writePoint registers scalarMultiple point) scalarMultiple = some point :=
  readPoint_writePoint registers scalarMultiple point (by decide) (by decide) (by decide)

/-- Updating the multiple preserves the accumulator. -/
theorem scalarAccumulator_other [BN254.FieldCertificate] (registers : Register → Word) (point : BN254.Point) :
    readPoint (writePoint registers scalarMultiple point) scalarAccumulator = readPoint registers scalarAccumulator := by
  apply readPoint_congr <;> apply writePoint_other <;> decide

/-- Updating the accumulator preserves the multiple. -/
theorem scalarMultiple_other [BN254.FieldCertificate] (registers : Register → Word) (point : BN254.Point) :
    readPoint (writePoint registers scalarAccumulator point) scalarMultiple = readPoint registers scalarMultiple := by
  apply readPoint_congr <;> apply writePoint_other <;> decide

/-- The loop charges five instructions for an even scalar and six for an odd scalar. -/
def scalarLoopCost (value : Nat) : Nat :=
  if zero : value = 0 then 2 else scalarLoopCost (value / 2) + 5 + value % 2
termination_by value
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)

/-- The loop cost grows by at most six instructions per scalar bit. -/
theorem scalarLoopCost_bound (value : Nat) : scalarLoopCost value ≤ 6 * bitLength value + 2 := by
  induction value using Nat.strong_induction_on with
  | h value ih =>
      by_cases zero : value = 0
      · subst value
        simp [scalarLoopCost, bitLength]
      · have positive := Nat.pos_of_ne_zero zero
        have shorter := Nat.div_lt_self positive (by decide : 1 < 2)
        have previous := ih (value / 2) shorter
        have bit := Nat.mod_lt value (by decide : 0 < 2)
        rw [scalarLoopCost, dif_neg zero, bitLength_step value positive]
        omega

/-- The loop records the conditional addition, the point doubling, and the scalar shift. -/
def scalarNext [BN254.FieldCertificate] (base : Memory) (value : Nat) (a b : BN254.Point) : Memory :=
  let marked := Function.update base.registers 8 (BitVec.ofNat 256 (value % 2))
  let accumulated := if value % 2 = 0 then marked else writePoint marked scalarAccumulator (a + b)
  let doubled := writePoint accumulated scalarMultiple (b + b)
  {base with registers := Function.update doubled 0 (BitVec.ofNat 256 (value / 2))}

/-- The loop tests zero and halts in two instructions. -/
theorem scalarMul_zero [BN254.FieldCertificate] (fuel : Nat) (base : Memory)
    (zero : base.registers 0 = 0#256) :
    run scalarMul (fuel + 2) ⟨4, base⟩ = PMF.pure (some (⟨10, base⟩, 2)) := by
  simp [run, step, scalarMul, zero, PMF.pure_map]
  rfl

/-- One nonzero iteration returns to the loop after its exact arithmetic cost. -/
theorem scalarMul_step [BN254.FieldCertificate] (fuel value : Nat) (base : Memory) (a b : BN254.Point)
    (positive : 0 < value) (fits : value < 2 ^ 256)
    (scalar : base.registers 0 = BitVec.ofNat 256 value) (one : base.registers 1 = 1#256)
    (accumulator : readPoint base.registers scalarAccumulator = some a)
    (multiple : readPoint base.registers scalarMultiple = some b) :
    run scalarMul (fuel + (5 + value % 2)) ⟨4, base⟩ =
      (run scalarMul fuel ⟨4, scalarNext base value a b⟩).map
        (Option.map fun result => (result.1, result.2 + (5 + value % 2))) := by
  have nonzero : BitVec.ofNat 256 value ≠ 0#256 := by
    intro equal
    have natural := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] at natural
    change value = 0 at natural
    omega
  have readAcc (registers : Register → Word) (word : Word) :
      readPoint (Function.update registers 8 word) scalarAccumulator = readPoint registers scalarAccumulator :=
    readPoint_update_other registers scalarAccumulator 8 word (by decide) (by decide) (by decide)
  have readMultiple (registers : Register → Word) (word : Word) :
      readPoint (Function.update registers 8 word) scalarMultiple = readPoint registers scalarMultiple :=
    readPoint_update_other registers scalarMultiple 8 word (by decide) (by decide) (by decide)
  have acc0 (registers : Register → Word) (point : BN254.Point) :
      writePoint registers scalarAccumulator point 0 = registers 0 :=
    writePoint_other registers scalarAccumulator point 0 (by decide) (by decide) (by decide)
  have acc1 (registers : Register → Word) (point : BN254.Point) :
      writePoint registers scalarAccumulator point 1 = registers 1 :=
    writePoint_other registers scalarAccumulator point 1 (by decide) (by decide) (by decide)
  have mul0 (registers : Register → Word) (point : BN254.Point) :
      writePoint registers scalarMultiple point 0 = registers 0 :=
    writePoint_other registers scalarMultiple point 0 (by decide) (by decide) (by decide)
  have mul1 (registers : Register → Word) (point : BN254.Point) :
      writePoint registers scalarMultiple point 1 = registers 1 :=
    writePoint_other registers scalarMultiple point 1 (by decide) (by decide) (by decide)
  rcases Nat.mod_two_eq_zero_or_one value with even | odd
  · simp only [even, Nat.add_zero]
    simp [run, step, scalarMul, Arithmetic.eval, scalar, one, nonzero, scalar_lowBit value fits,
      even, readAcc, readMultiple, accumulator, multiple, scalarNext,
      mul0, mul1, width_shift value fits,
      PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]
    rfl
  · simp only [odd]
    simp [run, step, scalarMul, Arithmetic.eval, scalar, one, nonzero, scalar_lowBit value fits,
      odd, readAcc, readMultiple, accumulator, multiple, scalarNext, scalarMultiple_other,
      acc0, acc1, mul0, mul1, width_shift value fits,
      PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]
    rfl

/-- One iteration preserves the scalar register invariant and the constant-one register. -/
theorem scalarNext_registers [BN254.FieldCertificate] (base : Memory) (value : Nat) (a b : BN254.Point)
    (one : base.registers 1 = 1#256) :
    (scalarNext base value a b).registers 0 = BitVec.ofNat 256 (value / 2) ∧
      (scalarNext base value a b).registers 1 = 1#256 := by
  constructor
  · simp [scalarNext]
  · dsimp only [scalarNext]
    rw [Function.update_of_ne (by decide : (1 : Register) ≠ 0),
      writePoint_other _ scalarMultiple _ 1 (by decide) (by decide) (by decide)]
    split
    · simpa using one
    · rw [writePoint_other _ scalarAccumulator _ 1 (by decide) (by decide) (by decide)]
      simpa using one

/-- One iteration records its exact accumulated point. -/
theorem scalarNext_accumulator [BN254.FieldCertificate] (base : Memory) (value : Nat) (a b : BN254.Point)
    (accumulator : readPoint base.registers scalarAccumulator = some a) :
    readPoint (scalarNext base value a b).registers scalarAccumulator =
      some (if value % 2 = 0 then a else a + b) := by
  dsimp only [scalarNext]
  rw [readPoint_update_other _ scalarAccumulator 0 _ (by decide) (by decide) (by decide),
    scalarAccumulator_other]
  split
  · rw [readPoint_update_other _ scalarAccumulator 8 _ (by decide) (by decide) (by decide)]
    exact accumulator
  · exact scalarAccumulator_write _ _

/-- One iteration doubles its current point multiple. -/
theorem scalarNext_multiple [BN254.FieldCertificate] (base : Memory) (value : Nat) (a b : BN254.Point) :
    readPoint (scalarNext base value a b).registers scalarMultiple = some (b + b) := by
  dsimp only [scalarNext]
  rw [readPoint_update_other _ scalarMultiple 0 _ (by decide) (by decide) (by decide)]
  exact scalarMultiple_write _ _

/-- The scalar decomposition preserves the accumulated group result. -/
theorem scalar_iteration_value [BN254.FieldCertificate] (value : Nat) (a b : BN254.Point) :
    (if value % 2 = 0 then a else a + b) + (value / 2) • (b + b) = a + value • b := by
  rcases Nat.mod_two_eq_zero_or_one value with even | odd
  · have decomposition : value = value / 2 + value / 2 := by omega
    rw [if_pos even, nsmul_add, ← add_nsmul, ← decomposition]
  · have decomposition : value = value / 2 + value / 2 + 1 := by omega
    rw [if_neg (by omega), nsmul_add]
    conv_rhs => rw [decomposition, add_nsmul, add_nsmul, one_nsmul]
    abel

/-- Each iteration preserves registers nine through fifteen. -/
theorem scalarNext_caller [BN254.FieldCertificate] (base : Memory) (value : Nat) (a b : BN254.Point)
    (register : Register) (caller : 9 ≤ register.val) :
    (scalarNext base value a b).registers register = base.registers register := by
  have different (target : Register) (localRegister : target.val < 9) : register ≠ target := by
    intro equal
    have values := congrArg Fin.val equal
    omega
  dsimp only [scalarNext]
  rw [Function.update_of_ne (different 0 (by decide)),
    writePoint_other _ scalarMultiple _ register
      (different 5 (by decide)) (different 6 (by decide)) (different 7 (by decide))]
  split
  · exact Function.update_of_ne (different 8 (by decide)) _ _
  · rw [writePoint_other _ scalarAccumulator _ register
      (different 2 (by decide)) (different 3 (by decide)) (different 4 (by decide))]
    exact Function.update_of_ne (different 8 (by decide)) _ _

/-- The complete loop returns the exact group result and the actual instruction cost. -/
theorem scalarMul_loop [BN254.FieldCertificate] (value fuel : Nat) (base : Memory) (a b : BN254.Point)
    (fits : value < 2 ^ 256) (scalar : base.registers 0 = BitVec.ofNat 256 value)
    (one : base.registers 1 = 1#256)
    (accumulator : readPoint base.registers scalarAccumulator = some a)
    (multiple : readPoint base.registers scalarMultiple = some b) :
    ∃ final : Memory,
      run scalarMul (scalarLoopCost value + fuel) ⟨4, base⟩ =
        PMF.pure (some (⟨10, final⟩, scalarLoopCost value)) ∧
      readPoint final.registers scalarAccumulator = some (a + value • b) ∧
      final.bits = base.bits ∧ final.ram = base.ram ∧
      ∀ register : Register, 9 ≤ register.val → final.registers register = base.registers register := by
  induction value using Nat.strong_induction_on generalizing base a b with
  | h value ih =>
      by_cases zero : value = 0
      · subst value
        refine ⟨base, ?_, ?_, rfl, rfl, ?_⟩
        · have zeroCost : scalarLoopCost 0 = 2 := by rw [scalarLoopCost, dif_pos rfl]
          simpa only [zeroCost, Nat.add_comm] using scalarMul_zero fuel base scalar
        · simpa only [zero_nsmul, add_zero] using accumulator
        · intros; rfl
      · have positive := Nat.pos_of_ne_zero zero
        have shorter := Nat.div_lt_self positive (by decide : 1 < 2)
        have registers := scalarNext_registers base value a b one
        obtain ⟨final, execution, decoded, bitStore, ram, caller⟩ := ih (value / 2) shorter (scalarNext base value a b)
          (if value % 2 = 0 then a else a + b) (b + b) (lt_trans shorter fits)
          registers.1 registers.2 (scalarNext_accumulator base value a b accumulator)
          (scalarNext_multiple base value a b)
        refine ⟨final, ?_, ?_, bitStore, ram, ?_⟩
        · have cost : scalarLoopCost value = scalarLoopCost (value / 2) + 5 + value % 2 := by
            rw [scalarLoopCost, dif_neg zero]
          have total : scalarLoopCost value + fuel =
              (scalarLoopCost (value / 2) + fuel) + (5 + value % 2) := by omega
          rw [total, scalarMul_step _ value base a b positive fits scalar one accumulator multiple, execution]
          simp only [PMF.pure_map, Option.map_some, ← Nat.add_assoc, ← cost]
        · rw [scalar_iteration_value] at decoded
          exact decoded
        · intro register outside
          exact (caller register outside).trans (scalarNext_caller base value a b register outside)

/-- Initialization sets the accumulated point to zero and preserves the input point. -/
def scalarInitialized (base : Memory) : Memory :=
  {base with registers := Function.update (Function.update (Function.update
    (Function.update base.registers 1 1) 2 0) 3 0) 4 0}

/-- The entry initializes the loop in four charged instructions. -/
theorem scalarMul_setup [BN254.FieldCertificate] (fuel : Nat) (base : Memory) :
    run scalarMul (fuel + 4) ⟨0, base⟩ =
      (run scalarMul fuel ⟨4, scalarInitialized base⟩).map
        (Option.map fun result => (result.1, result.2 + 4)) := by
  simp [run, step, scalarMul, scalarInitialized, PMF.map_comp, Option.map_map,
    Function.comp_def, Nat.add_assoc]
  rfl

/-- Initialization preserves the input point decoder. -/
theorem scalarInitialized_multiple [BN254.FieldCertificate] (base : Memory) :
    readPoint (scalarInitialized base).registers scalarMultiple = readPoint base.registers scalarMultiple := by
  dsimp only [scalarInitialized]
  rw [readPoint_update_other _ scalarMultiple 4 _ (by decide) (by decide) (by decide),
    readPoint_update_other _ scalarMultiple 3 _ (by decide) (by decide) (by decide),
    readPoint_update_other _ scalarMultiple 2 _ (by decide) (by decide) (by decide),
    readPoint_update_other _ scalarMultiple 1 _ (by decide) (by decide) (by decide)]

/-- A machine word has at most 256 significant bits. -/
theorem scalar_word_bits (word : Word) : bitLength word.toNat ≤ 256 := by
  by_cases zero : word = 0#256
  · simp [zero, bitLength]
  · simpa only [lowWidth, if_neg zero] using lowWidth_bound word

/-- Every scalar multiplication uses at most 1542 instructions. -/
theorem scalarMul_instruction_bound (word : Word) : scalarLoopCost word.toNat + 4 ≤ 1542 := by
  have loop := scalarLoopCost_bound word.toNat
  have bits := scalar_word_bits word
  omega

/-- The fixed-budget machine returns the exact scalar multiple and preserves caller data. -/
theorem scalarMul_run [BN254.FieldCertificate] (base : Memory) (point : BN254.Point)
    (input : readPoint base.registers scalarMultiple = some point) :
    ∃ final : Memory,
      run scalarMul 1542 ⟨0, base⟩ =
        PMF.pure (some (⟨10, final⟩, scalarLoopCost (base.registers 0).toNat + 4)) ∧
      readPoint final.registers scalarAccumulator = some ((base.registers 0).toNat • point) ∧
      final.bits = base.bits ∧ final.ram = base.ram ∧
      ∀ register : Register, 9 ≤ register.val → final.registers register = base.registers register := by
  let value := (base.registers 0).toNat
  have bounded := scalarMul_instruction_bound (base.registers 0)
  have scalar : (scalarInitialized base).registers 0 = BitVec.ofNat 256 value := by
    simp [scalarInitialized, value]
  have one : (scalarInitialized base).registers 1 = 1#256 := by simp [scalarInitialized]
  have accumulator : readPoint (scalarInitialized base).registers scalarAccumulator = some (0 : BN254.Point) := by
    simp [scalarInitialized, scalarAccumulator, readPoint]
  have multiple : readPoint (scalarInitialized base).registers scalarMultiple = some point :=
    (scalarInitialized_multiple base).trans input
  obtain ⟨final, execution, decoded, bitStore, ram, caller⟩ := scalarMul_loop value
    (1542 - (scalarLoopCost value + 4)) (scalarInitialized base) 0 point (base.registers 0).isLt
    scalar one accumulator multiple
  refine ⟨final, ?_, ?_, bitStore, ram, ?_⟩
  · have total : 1542 = (scalarLoopCost value + (1542 - (scalarLoopCost value + 4))) + 4 := by
      change scalarLoopCost value + 4 ≤ 1542 at bounded
      omega
    rw [total, scalarMul_setup, execution]
    simp only [PMF.pure_map, Option.map_some]
    rfl
  · simpa only [zero_add] using decoded
  · intro register outside
    have different (target : Register) (localRegister : target.val < 9) : register ≠ target := by
      intro equal
      have values := congrArg Fin.val equal
      omega
    rw [caller register outside]
    dsimp only [scalarInitialized]
    rw [Function.update_of_ne (different 4 (by decide)), Function.update_of_ne (different 3 (by decide)),
      Function.update_of_ne (different 2 (by decide)), Function.update_of_ne (different 1 (by decide))]

/-- Reading the result gives the exact natural-number scalar action. -/
theorem scalarMul_source [BN254.FieldCertificate] (base : Memory) (point : BN254.Point)
    (input : readPoint base.registers scalarMultiple = some point) :
    (run scalarMul 1542 ⟨0, base⟩).map
      (fun result => result.bind fun final => readPoint final.1.memory.registers scalarAccumulator) =
      PMF.pure (some ((base.registers 0).toNat • point)) := by
  obtain ⟨final, execution, decoded, _⟩ := scalarMul_run base point input
  rw [execution]
  simp only [PMF.pure_map, Option.bind_some, decoded]

/-- Canonical scalar-field input gives the certified BN254 scalar action. -/
theorem scalarMul_field [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (scalar : BN254.ScalarField) (point : BN254.Point)
    (scalarInput : base.registers 0 = BitVec.ofNat 256 scalar.val)
    (pointInput : readPoint base.registers scalarMultiple = some point) :
    (run scalarMul 1542 ⟨0, base⟩).map
      (fun result => result.bind fun final => readPoint final.1.memory.registers scalarAccumulator) =
      PMF.pure (some (scalar • point)) := by
  rw [scalarMul_source base point pointInput, scalarInput]
  have fits : scalar.val < 2 ^ 256 :=
    lt_trans scalar.val_lt (by decide : BN254.scalarFieldModulus < 2 ^ 256)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
  have cast : (scalar.val : BN254.ScalarField) = scalar := ZMod.natCast_zmod_val scalar
  conv_rhs => rw [← cast, Nat.cast_smul_eq_nsmul]

/-- The instruction budget and the full control table cost at most 1553 units. -/
theorem scalarMul_totalCost : 1542 + scalarMul.size + 1 = 1553 := rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
