import Proof.Privacy.Simulator.Arithmetic.RetargetSchedule

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine

/-- The input pass computes the four exact polynomial factors. -/
theorem retargetInput_values (memory : Memory) (input : AffineInput)
    (coordinates : memory.ram (memory.registers 12) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (memory.registers 12 + 1) = BitVec.ofNat 256 input.y.val) :
    ∀ factor, (executeLinear retargetInput memory).registers (polynomialFactorRegister factor) =
      BitVec.ofNat 256 (polynomialInput input factor).val := by
  have yword : memory.ram (memory.registers 12 + 1#256) = BitVec.ofNat 256 input.y.val := coordinates.2
  intro factor
  fin_cases factor <;>
    simp [retargetInput, polynomialInput, polynomialFactorRegister, executeLinear,
      LinearInstruction.execute, show Arithmetic.add.eval = (· + ·) from rfl, coordinates,
      yword, fieldMul_words, pow_two]

/-- The input pass preserves RAM, stacks, and caller pointers. -/
theorem retargetInput_preserves (memory : Memory) :
    (executeLinear retargetInput memory).ram = memory.ram ∧
    (executeLinear retargetInput memory).bits = memory.bits ∧
    ∀ register : Register, 9 ≤ register.val →
      (executeLinear retargetInput memory).registers register = memory.registers register := by
  refine ⟨rfl, rfl, ?_⟩
  intro register caller
  have different (target : Register) (small : target.val < 9) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [retargetInput, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne (different 2 (by decide)), Function.update_of_ne (different 5 (by decide)),
    Function.update_of_ne (different 6 (by decide)), Function.update_of_ne (different 7 (by decide)),
    Function.update_of_ne (different 8 (by decide))]

/-- The request prefix selects the source and target pointers without changing RAM. -/
def retargetAtPrepared (sourceOffset : Nat) (targetBase : Register) (targetOffset : Nat) (memory : Memory) : Memory :=
  {memory with
    registers := Function.update
      (Function.update memory.registers 10 (memory.registers 11 + BitVec.ofNat 256 sourceOffset))
      13 (memory.registers targetBase + BitVec.ofNat 256 targetOffset)}

/-- The fixed request prefix implements its exact pointer source. -/
theorem retargetAt_memory (kind : RetargetKind) (sourceOffset : Nat) (targetBase : Register) (targetOffset : Nat)
    (memory : Memory) (notTen : targetBase ≠ 10) (notThirteen : targetBase ≠ 13) :
    executeLinear (retargetAt kind sourceOffset targetBase targetOffset) memory =
      executeLinear (retargetCode kind) (retargetAtPrepared sourceOffset targetBase targetOffset memory) := by
  rw [retargetAt, executeLinear_append]
  congr 1
  simp [executeLinear, LinearInstruction.execute, Arithmetic.eval, retargetAtPrepared, notTen, notThirteen]

attribute [local irreducible] gateRetarget gatePolynomial polynomial

private def CallerPreserved (program : List LinearInstruction) (memory : Memory) : Prop :=
  (executeLinear program memory).bits = memory.bits ∧
    ∀ register : Register, 5 ≤ register.val →
      (executeLinear program memory).registers register = memory.registers register

private theorem retargetCallerPreserved {coefficients gates : Nat} (terms : List (GateTerm coefficients gates))
    (gate : Fin gates) (memory : Memory) : CallerPreserved (gateRetarget terms gate) memory :=
  gateRetarget_preserves terms gate memory

private theorem retargetProgramCallerPreserved (kind : RetargetKind) (memory : Memory) :
    CallerPreserved (retargetProgram kind) memory := by
  cases kind
  · exact retargetCallerPreserved curveTerms 2 memory
  · exact retargetCallerPreserved xTerms 3 memory
  · exact retargetCallerPreserved yTerms 2 memory
  · exact retargetCallerPreserved zTerms 4 memory

private theorem retargetCodeCallerPreserved (kind : RetargetKind) (memory : Memory) :
    CallerPreserved (retargetCode kind) memory := by
  rw [retargetCode_eq]
  exact retargetProgramCallerPreserved kind memory

/-- Every request retains its polynomial factors and caller pointers after its arithmetic. -/
theorem retargetCode_preserves (kind : RetargetKind) (memory : Memory) :
    (executeLinear (retargetCode kind) memory).bits = memory.bits ∧
    ∀ register : Register, 5 ≤ register.val →
      (executeLinear (retargetCode kind) memory).registers register = memory.registers register :=
  retargetCodeCallerPreserved kind memory

/-- The complete selected request retains all caller registers except its two work pointers. -/
theorem retargetAt_preserves (kind : RetargetKind) (sourceOffset : Nat) (targetBase : Register) (targetOffset : Nat)
    (memory : Memory) (notTen : targetBase ≠ 10) (notThirteen : targetBase ≠ 13) :
    (executeLinear (retargetAt kind sourceOffset targetBase targetOffset) memory).bits = memory.bits ∧
    ∀ register : Register, 5 ≤ register.val → register ≠ 10 → register ≠ 13 →
      (executeLinear (retargetAt kind sourceOffset targetBase targetOffset) memory).registers register = memory.registers register := by
  rw [retargetAt_memory kind sourceOffset targetBase targetOffset memory notTen notThirteen]
  have saved := retargetCode_preserves kind (retargetAtPrepared sourceOffset targetBase targetOffset memory)
  refine ⟨saved.1, ?_⟩
  intro register lower first second
  rw [saved.2 register lower]
  simp only [retargetAtPrepared, Function.update_of_ne first, Function.update_of_ne second]

/-- A pointer shift retains the exact word-list representation. -/
theorem wordsAt_rebase {ram : Word → Word} {pointer : Word} {start : Nat} {words : List Word}
    (stored : WordsAt ram pointer start words) :
    WordsAt ram (pointer + BitVec.ofNat 256 start) 0 words := by
  intro index inside
  simpa only [Nat.zero_add, BitVec.ofNat_add, BitVec.add_assoc] using stored index inside

end Kriterion.ArgoMAC.ArithmeticSimulator
