import Proof.Privacy.Simulator.Arithmetic.RetargetFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] retargetAt retargetInput

/-- The complete curve pass preserves every word outside its low-target update. -/
theorem retargetCurveCode_outside (memory : Memory) (address : Word)
    (outside : address ≠ memory.registers 11 + 834903) :
    (executeLinear retargetCurveCode memory).ram address = memory.ram address := by
  rw [retargetCurveCode_eq, retargetCurveProgram, executeLinear_append]
  have saved := retargetInput_preserves memory
  rw [retargetAt_outside .curve 834395 11 0 (executeLinear retargetInput memory)
    (by decide) (by decide) address]
  · exact congrFun saved.1 address
  · rw [saved.2.2 11 (by decide)]
    have same : memory.registers 11 + BitVec.ofNat 256 834395 +
        BitVec.ofNat 256 (retargetLowOffset .curve) = memory.registers 11 + 834903 := by
      rw [BitVec.add_assoc]
      rfl
    rw [same]
    exact outside

/-- The complete curve pass preserves the source and selected-input pointers. -/
theorem retargetCurveCode_caller (memory : Memory) (register : Register)
    (caller : 11 ≤ register.val) (notTarget : register ≠ 13) :
    (executeLinear retargetCurveCode memory).registers register = memory.registers register := by
  rw [retargetCurveCode_eq, retargetCurveProgram, executeLinear_append]
  have saved := retargetAt_preserves .curve 834395 11 0 (executeLinear retargetInput memory)
    (by decide) (by decide)
  rw [saved.2 register (by omega) (by intro equal; subst register; simp at caller) notTarget]
  exact (retargetInput_preserves memory).2.2 register (by omega)

end Kriterion.ArgoMAC.ArithmeticSimulator
