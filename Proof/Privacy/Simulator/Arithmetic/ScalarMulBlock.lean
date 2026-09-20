import Proof.Privacy.Simulator.Arithmetic.ScalarMul
import Construction.Simulator.Assembly

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host contains every scalar-multiplication instruction before its return. -/
def ContainsScalarMul (host : Machine) (labels : Fin 11 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 11, pc.val < 10 → host.code[(labels pc).val] =
    relocate labels (scalarMul.code[pc.val]'(by exact pc.isLt))

/-- The zero scalar returns after one guard instruction. -/
theorem scalarMulBlock_zero [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 11 → Fin (host.size + 1)) (present : ContainsScalarMul host labels)
    (base : Memory) (zero : base.registers 0 = 0#256) :
    runPrefix host 1 ⟨labels 4, base⟩ = PMF.pure (some (false, ⟨labels 10, base⟩, 1)) := by
  simp [runPrefix, step, present 4 (by decide), scalarMul, relocate, zero, PMF.pure_map]

/-- The loop always pays for its guard and halt. -/
theorem scalarLoopCost_positive (value : Nat) : 2 ≤ scalarLoopCost value := by
  rw [scalarLoopCost]
  split <;> omega

/-- One nonzero iteration returns to the loop after its exact arithmetic cost. -/
theorem scalarMulBlock_step [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 11 → Fin (host.size + 1)) (present : ContainsScalarMul host labels) (fuel value : Nat) (base : Memory) (a b : BN254.Point)
    (positive : 0 < value) (fits : value < 2 ^ 256)
    (scalar : base.registers 0 = BitVec.ofNat 256 value) (one : base.registers 1 = 1#256)
    (accumulator : readPoint base.registers scalarAccumulator = some a)
    (multiple : readPoint base.registers scalarMultiple = some b) :
    runPrefix host (fuel + (5 + value % 2)) ⟨labels 4, base⟩ =
      (runPrefix host fuel ⟨labels 4, scalarNext base value a b⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + (5 + value % 2))) := by
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
    simp [runPrefix, step, present 4 (by decide), present 5 (by decide),
      present 6 (by decide), present 7 (by decide), present 8 (by decide), present 9 (by decide),
      scalarMul, relocate, Arithmetic.eval, scalar, one, nonzero, scalar_lowBit value fits,
      even, readAcc, readMultiple, accumulator, multiple, scalarNext,
      mul0, mul1, width_shift value fits,
      PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]
  · simp only [odd]
    simp [runPrefix, step, present 4 (by decide), present 5 (by decide),
      present 6 (by decide), present 7 (by decide), present 8 (by decide), present 9 (by decide),
      scalarMul, relocate, Arithmetic.eval, scalar, one, nonzero, scalar_lowBit value fits,
      odd, readAcc, readMultiple, accumulator, multiple, scalarNext, scalarMultiple_other,
      acc0, acc1, mul0, mul1, width_shift value fits,
      PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]


/-- The complete loop returns the exact group result and the actual instruction cost. -/
theorem scalarMulBlock_loop [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 11 → Fin (host.size + 1)) (present : ContainsScalarMul host labels) (value : Nat) (base : Memory) (a b : BN254.Point)
    (fits : value < 2 ^ 256) (scalar : base.registers 0 = BitVec.ofNat 256 value)
    (one : base.registers 1 = 1#256)
    (accumulator : readPoint base.registers scalarAccumulator = some a)
    (multiple : readPoint base.registers scalarMultiple = some b) :
    ∃ final : Memory,
      runPrefix host (scalarLoopCost value - 1) ⟨labels 4, base⟩ =
        PMF.pure (some (false, ⟨labels 10, final⟩, scalarLoopCost value - 1)) ∧
      readPoint final.registers scalarAccumulator = some (a + value • b) ∧
      final.bits = base.bits ∧ final.ram = base.ram ∧
      ∀ register : Register, 9 ≤ register.val → final.registers register = base.registers register := by
  induction value using Nat.strong_induction_on generalizing base a b with
  | h value ih =>
      by_cases zero : value = 0
      · subst value
        refine ⟨base, ?_, ?_, rfl, rfl, ?_⟩
        · have zeroCost : scalarLoopCost 0 = 2 := by rw [scalarLoopCost, dif_pos rfl]
          simpa only [zeroCost, show 2 - 1 = 1 from rfl] using scalarMulBlock_zero host labels present base scalar
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
          have positiveCost := scalarLoopCost_positive (value / 2)
          have total : scalarLoopCost value - 1 =
              (scalarLoopCost (value / 2) - 1) + (5 + value % 2) := by omega
          rw [total, scalarMulBlock_step host labels present _ value base a b positive fits scalar one accumulator multiple, execution]
          simp only [PMF.pure_map, Option.map_some]
        · rw [scalar_iteration_value] at decoded
          exact decoded
        · intro register outside
          exact (caller register outside).trans (scalarNext_caller base value a b register outside)


/-- The embedded entry initializes the accumulator in four instructions. -/
theorem scalarMulBlock_setup [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 11 → Fin (host.size + 1)) (present : ContainsScalarMul host labels)
    (fuel : Nat) (base : Memory) :
    runPrefix host (fuel + 4) ⟨labels 0, base⟩ =
      (runPrefix host fuel ⟨labels 4, scalarInitialized base⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 4)) := by
  simp [runPrefix, step, present 0 (by decide), present 1 (by decide), present 2 (by decide),
    present 3 (by decide), scalarMul, relocate, scalarInitialized, PMF.map_comp, Option.map_map,
    Function.comp_def, Nat.add_assoc]

/-- The embedded machine returns before the host instruction and retains its exact cost. -/
theorem scalarMulBlock_prefix [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 11 → Fin (host.size + 1)) (present : ContainsScalarMul host labels)
    (base : Memory) (point : BN254.Point)
    (input : readPoint base.registers scalarMultiple = some point) :
    ∃ final : Memory,
      runPrefix host (scalarLoopCost (base.registers 0).toNat + 3) ⟨labels 0, base⟩ =
        PMF.pure (some (false, ⟨labels 10, final⟩, scalarLoopCost (base.registers 0).toNat + 3)) ∧
      readPoint final.registers scalarAccumulator = some ((base.registers 0).toNat • point) ∧
      final.bits = base.bits ∧ final.ram = base.ram ∧
      ∀ register : Register, 9 ≤ register.val → final.registers register = base.registers register := by
  let value := (base.registers 0).toNat
  have scalar : (scalarInitialized base).registers 0 = BitVec.ofNat 256 value := by
    simp [scalarInitialized, value]
  have one : (scalarInitialized base).registers 1 = 1#256 := by simp [scalarInitialized]
  have accumulator : readPoint (scalarInitialized base).registers scalarAccumulator = some (0 : BN254.Point) := by
    simp [scalarInitialized, scalarAccumulator, readPoint]
  have multiple : readPoint (scalarInitialized base).registers scalarMultiple = some point :=
    (scalarInitialized_multiple base).trans input
  obtain ⟨final, execution, decoded, bitStore, ram, caller⟩ := scalarMulBlock_loop host labels present value
    (scalarInitialized base) 0 point (base.registers 0).isLt scalar one accumulator multiple
  refine ⟨final, ?_, ?_, bitStore, ram, ?_⟩
  · have positiveCost := scalarLoopCost_positive value
    have total : scalarLoopCost value + 3 = (scalarLoopCost value - 1) + 4 := by omega
    change runPrefix host (scalarLoopCost value + 3) ⟨labels 0, base⟩ = _
    rw [total, scalarMulBlock_setup host labels present, execution]
    simp only [PMF.pure_map, Option.map_some]
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

/-- The host resumes after scalar multiplication and retains every remaining fuel unit. -/
theorem scalarMulBlock_run [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 11 → Fin (host.size + 1)) (present : ContainsScalarMul host labels)
    (fuel : Nat) (base : Memory) (point : BN254.Point)
    (input : readPoint base.registers scalarMultiple = some point) :
    ∃ final : Memory,
      run host (scalarLoopCost (base.registers 0).toNat + 3 + fuel) ⟨labels 0, base⟩ =
        (run host fuel ⟨labels 10, final⟩).map
          (Option.map fun result => (result.1, result.2 + (scalarLoopCost (base.registers 0).toNat + 3))) ∧
      readPoint final.registers scalarAccumulator = some ((base.registers 0).toNat • point) ∧
      final.bits = base.bits ∧ final.ram = base.ram ∧
      ∀ register : Register, 9 ≤ register.val → final.registers register = base.registers register := by
  obtain ⟨final, execution, decoded, bitStore, ram, caller⟩ := scalarMulBlock_prefix host labels present base point input
  refine ⟨final, ?_, decoded, bitStore, ram, caller⟩
  rw [run_after_prefix, execution, PMF.pure_bind]

end Kriterion.ArgoMAC.ArithmeticSimulator
