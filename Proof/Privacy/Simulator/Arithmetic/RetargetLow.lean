import Construction.Simulator.RetargetLow
import Proof.Privacy.Simulator.Arithmetic.FieldFoldStep
import Proof.Privacy.Programming.ProgrammingBridge

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The source retarget operation changes only the low target by the result difference. -/
theorem retargetBits_low {count : Nat} (values : Fin (count + 1) → BN254.BaseField)
    (target result : BN254.BaseField) :
    Security.retargetBits values (target - result + DigitAdaptor.fromBits values) 0 = target - result + values 0 := by
  simp only [Security.retargetBits, Fin.cases_zero, DigitAdaptor.fromBits, Fin.foldr_succ]
  ring

/-- The source retarget operation preserves every free target. -/
theorem retargetBits_high {count : Nat} (values : Fin (count + 1) → BN254.BaseField)
    (target : BN254.BaseField) (index : Fin count) :
    Security.retargetBits values target index.succ = values index.succ := by
  simp [Security.retargetBits]

/-- The low-target machine uses four fixed instructions. -/
theorem retargetLow_length : retargetLow.length = 4 := rfl

/-- The low-target machine returns the exact canonical field update. -/
theorem retargetLow_value (base : Memory) (target result old : BN254.BaseField)
    (targetWord : base.registers 0 = BitVec.ofNat 256 target.val)
    (resultWord : base.registers 1 = BitVec.ofNat 256 result.val)
    (oldWord : base.ram (base.registers 10) = BitVec.ofNat 256 old.val) :
    (executeLinear retargetLow base).registers 0 = BitVec.ofNat 256 (target - result + old).val := by
  simp only [retargetLow, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute]
  simp only [Function.update_self, Function.update_of_ne (by decide : (0 : Register) ≠ 2),
    Function.update_of_ne (by decide : (1 : Register) ≠ 2),
    Function.update_of_ne (by decide : (2 : Register) ≠ 0), targetWord, resultWord, oldWord,
    fieldSub_words, fieldAdd_words]

/-- The low-target machine preserves the protocol stacks and all registers above two. -/
theorem retargetLow_preserves (base : Memory) :
    (executeLinear retargetLow base).bits = base.bits ∧
    ∀ register : Register, 3 ≤ register.val → (executeLinear retargetLow base).registers register = base.registers register := by
  refine ⟨rfl, ?_⟩
  intro register caller
  have different (target : Register) (small : target.val < 3) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [retargetLow, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne (different 0 (by decide)), Function.update_of_ne (different 2 (by decide))]

/-- The low-target machine writes only its designated target word. -/
theorem retargetLow_ram (base : Memory) :
    (executeLinear retargetLow base).ram = Function.update base.ram (base.registers 10)
      ((executeLinear retargetLow base).registers 0) := by
  simp [retargetLow, executeLinear, LinearInstruction.execute]

end Kriterion.ArgoMAC.ArithmeticSimulator
