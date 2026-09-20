import Proof.Privacy.Simulator.Arithmetic.ScalarMulBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- This deterministic law records the memory after the scalar loop. -/
def scalarLoopMemory [BN254.FieldCertificate] (value : Nat) (base : Memory) (a b : BN254.Point) : Memory :=
  if zero : value = 0 then base else
    scalarLoopMemory (value / 2) (scalarNext base value a b)
      (if value % 2 = 0 then a else a + b) (b + b)
termination_by value
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)

/-- The scalar loop has an exact deterministic memory law. -/
theorem scalarMulBlock_loop_memory [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 11 → Fin (host.size + 1)) (present : ContainsScalarMul host labels)
    (value : Nat) (base : Memory) (a b : BN254.Point) (fits : value < 2 ^ 256)
    (scalar : base.registers 0 = BitVec.ofNat 256 value) (one : base.registers 1 = 1#256)
    (accumulator : readPoint base.registers scalarAccumulator = some a)
    (multiple : readPoint base.registers scalarMultiple = some b) :
    runPrefix host (scalarLoopCost value - 1) ⟨labels 4, base⟩ =
      PMF.pure (some (false, ⟨labels 10, scalarLoopMemory value base a b⟩, scalarLoopCost value - 1)) := by
  induction value using Nat.strong_induction_on generalizing base a b with
  | h value ih =>
      by_cases zero : value = 0
      · subst value
        have zeroCost : scalarLoopCost 0 = 2 := by rw [scalarLoopCost, dif_pos rfl]
        have zeroMemory : scalarLoopMemory 0 base a b = base := by rw [scalarLoopMemory, dif_pos rfl]
        rw [zeroCost, zeroMemory]
        exact scalarMulBlock_zero host labels present base scalar
      · have positive := Nat.pos_of_ne_zero zero
        have shorter := Nat.div_lt_self positive (by decide : 1 < 2)
        have registers := scalarNext_registers base value a b one
        have previous := ih (value / 2) shorter (scalarNext base value a b)
          (if value % 2 = 0 then a else a + b) (b + b) (lt_trans shorter fits)
          registers.1 registers.2 (scalarNext_accumulator base value a b accumulator)
          (scalarNext_multiple base value a b)
        have cost : scalarLoopCost value = scalarLoopCost (value / 2) + 5 + value % 2 := by
          rw [scalarLoopCost, dif_neg zero]
        have positiveCost := scalarLoopCost_positive (value / 2)
        have total : scalarLoopCost value - 1 = (scalarLoopCost (value / 2) - 1) + (5 + value % 2) := by omega
        rw [total, scalarMulBlock_step host labels present _ value base a b positive fits scalar one accumulator multiple, previous]
        simp only [PMF.pure_map, Option.map_some]
        conv_rhs => rw [scalarLoopMemory, dif_neg zero]

/-- The complete scalar block initializes its exact loop-memory law. -/
def scalarFinish [BN254.FieldCertificate] (base : Memory) (point : BN254.Point) : Memory :=
  scalarLoopMemory (base.registers 0).toNat (scalarInitialized base) 0 point

/-- The complete scalar block returns its exact memory before the caller instruction. -/
theorem scalarMulBlock_memory [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 11 → Fin (host.size + 1)) (present : ContainsScalarMul host labels)
    (base : Memory) (point : BN254.Point) (input : readPoint base.registers scalarMultiple = some point) :
    runPrefix host (scalarLoopCost (base.registers 0).toNat + 3) ⟨labels 0, base⟩ =
      PMF.pure (some (false, ⟨labels 10, scalarFinish base point⟩, scalarLoopCost (base.registers 0).toNat + 3)) := by
  have scalar : (scalarInitialized base).registers 0 = BitVec.ofNat 256 (base.registers 0).toNat := by
    simp [scalarInitialized]
  have one : (scalarInitialized base).registers 1 = 1#256 := by simp [scalarInitialized]
  have accumulator : readPoint (scalarInitialized base).registers scalarAccumulator = some (0 : BN254.Point) := by
    simp [scalarInitialized, scalarAccumulator, readPoint]
  have multiple : readPoint (scalarInitialized base).registers scalarMultiple = some point :=
    (scalarInitialized_multiple base).trans input
  have loop := scalarMulBlock_loop_memory host labels present (base.registers 0).toNat (scalarInitialized base)
    0 point (base.registers 0).isLt scalar one accumulator multiple
  have positive := scalarLoopCost_positive (base.registers 0).toNat
  have total : scalarLoopCost (base.registers 0).toNat + 3 =
      (scalarLoopCost (base.registers 0).toNat - 1) + 4 := by omega
  rw [total, scalarMulBlock_setup host labels present, loop]
  simp only [PMF.pure_map, Option.map_some, scalarFinish]

/-- The exact scalar memory has the proved point value and preserves caller data. -/
theorem scalarFinish_spec [BN254.FieldCertificate] (base : Memory) (point : BN254.Point)
    (input : readPoint base.registers scalarMultiple = some point) :
    readPoint (scalarFinish base point).registers scalarAccumulator = some ((base.registers 0).toNat • point) ∧
    (scalarFinish base point).bits = base.bits ∧ (scalarFinish base point).ram = base.ram ∧
    ∀ register : Register, 9 ≤ register.val → (scalarFinish base point).registers register = base.registers register := by
  have present : ContainsScalarMul scalarMul id := by
    intro pc inside
    change scalarMul.code[pc.val] = relocate id (scalarMul.code[pc.val])
    generalize scalarMul.code[pc.val] = instruction
    cases instruction <;> rfl
  have exactMemory := scalarMulBlock_memory scalarMul id present base point input
  obtain ⟨final, execution, decoded, bitStore, ram, caller⟩ := scalarMulBlock_prefix scalarMul id present base point input
  rw [exactMemory] at execution
  have equal := congrArg PMF.support execution
  simp only [PMF.support_pure, Set.singleton_eq_singleton_iff] at equal
  have state := congrArg (fun result : Option (Bool × Configuration (scalarMul.size + 1) × Nat) =>
    result.map fun outcome => outcome.2.1.memory) equal
  have same : scalarFinish base point = final := Option.some.inj state
  rw [same]
  exact ⟨decoded, bitStore, ram, caller⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
