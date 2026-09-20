import Construction.Simulator.GateRetarget
import Proof.Privacy.Simulator.Arithmetic.RetargetLow

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Preparation loads the requested result and the computed old result. -/
theorem gateRetargetPrepare_spec (offset : Nat) (base : Memory) :
    (executeLinear (gateRetargetPrepare offset) base).ram = base.ram ∧
    (executeLinear (gateRetargetPrepare offset) base).registers 0 = base.ram (base.registers 13) ∧
    (executeLinear (gateRetargetPrepare offset) base).registers 1 = base.registers 4 ∧
    (executeLinear (gateRetargetPrepare offset) base).registers 10 = base.registers 10 + BitVec.ofNat 256 offset := by
  simp [gateRetargetPrepare, executeLinear, LinearInstruction.execute, Arithmetic.eval]

/-- The pointer return preserves the updated RAM. -/
theorem gateRetargetRestore_ram (offset : Nat) (base : Memory) :
    (executeLinear (gateRetargetRestore offset) base).ram = base.ram := rfl

/-- The retarget tail writes exactly the source's low-word update. -/
theorem gateRetargetFinish_ram (offset : Nat) (base : Memory) (target result old : BN254.BaseField)
    (computed : base.registers 4 = BitVec.ofNat 256 result.val)
    (requested : base.ram (base.registers 13) = BitVec.ofNat 256 target.val)
    (oldWord : base.ram (base.registers 10 + BitVec.ofNat 256 offset) = BitVec.ofNat 256 old.val) :
    (executeLinear (gateRetargetFinish offset) base).ram =
      Function.update base.ram (base.registers 10 + BitVec.ofNat 256 offset) (BitVec.ofNat 256 (target - result + old).val) := by
  have prepared := gateRetargetPrepare_spec offset base
  have resultWord := retargetLow_value (executeLinear (gateRetargetPrepare offset) base) target result old
    (prepared.2.1.trans requested) (prepared.2.2.1.trans computed)
    (by rw [prepared.1, prepared.2.2.2]; exact oldWord)
  rw [gateRetargetFinish, executeLinear_append, executeLinear_append, gateRetargetRestore_ram,
    retargetLow_ram, resultWord, prepared.1, prepared.2.2.2]

/-- The retarget tail preserves all protocol stacks. -/
theorem gateRetargetFinish_bits (offset : Nat) (base : Memory) :
    (executeLinear (gateRetargetFinish offset) base).bits = base.bits := by
  simp [gateRetargetFinish, gateRetargetPrepare, retargetLow, gateRetargetRestore,
    executeLinear, LinearInstruction.execute]

/-- The retarget tail restores register ten and preserves every higher register. -/
theorem gateRetargetFinish_caller (offset : Nat) (base : Memory) (register : Register) (caller : 5 ≤ register.val) :
    (executeLinear (gateRetargetFinish offset) base).registers register = base.registers register := by
  by_cases ten : register = 10
  · subst register
    simp [gateRetargetFinish, gateRetargetPrepare, retargetLow, gateRetargetRestore,
      executeLinear, LinearInstruction.execute, Arithmetic.eval]
  · have different (target : Register) (small : target.val < 5) : register ≠ target := by
      intro same; have value := congrArg Fin.val same; omega
    simp only [gateRetargetFinish, gateRetargetPrepare, retargetLow, gateRetargetRestore,
      executeLinear, List.foldl_append, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
      Function.update_of_ne ten, Function.update_of_ne (different 0 (by decide)),
      Function.update_of_ne (different 1 (by decide)), Function.update_of_ne (different 2 (by decide)),
      Function.update_of_ne (different 3 (by decide))]

/-- The retarget tail charges all eleven instructions. -/
theorem gateRetargetFinish_length (offset : Nat) : (gateRetargetFinish offset).length = 11 := by
  simp [gateRetargetFinish, gateRetargetPrepare, retargetLow, gateRetargetRestore]

end Kriterion.ArgoMAC.ArithmeticSimulator
