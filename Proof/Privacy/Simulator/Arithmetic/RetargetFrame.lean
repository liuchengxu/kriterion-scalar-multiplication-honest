import Proof.Privacy.Simulator.Arithmetic.RetargetScheduleMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The retarget tail changes no RAM word outside its designated low target. -/
theorem gateRetargetFinish_outside (offset : Nat) (memory : Memory) (address : Word)
    (outside : address ≠ memory.registers 10 + BitVec.ofNat 256 offset) :
    (executeLinear (gateRetargetFinish offset) memory).ram address = memory.ram address := by
  have prepared := gateRetargetPrepare_spec offset memory
  rw [gateRetargetFinish, executeLinear_append, executeLinear_append, gateRetargetRestore_ram,
    retargetLow_ram, prepared.1, prepared.2.2.2, Function.update_of_ne outside]

/-- The complete polynomial update changes only its designated low target. -/
theorem gateRetarget_outside {coefficients gates : Nat} (terms : List (GateTerm coefficients gates))
    (gate : Fin gates) (memory : Memory) (address : Word)
    (outside : address ≠ memory.registers 10 + BitVec.ofNat 256 (254 * gate.val)) :
    (executeLinear (gateRetarget terms gate) memory).ram address = memory.ram address := by
  have preserved := polynomial_preserves (terms.map GateTerm.compile) memory
  change (executeLinear (gatePolynomial terms) memory).ram = memory.ram ∧
    (executeLinear (gatePolynomial terms) memory).bits = memory.bits ∧
    (∀ register : Register, 5 ≤ register.val → (executeLinear (gatePolynomial terms) memory).registers register = memory.registers register) at preserved
  rw [gateRetarget, executeLinear_append, gateRetargetFinish_outside]
  · rw [preserved.1]
  · rw [preserved.2.2 10 (by decide)]
    exact outside

/-- Each request form selects one fixed low target. -/
def retargetLowOffset : RetargetKind → Nat
  | .curve => 508
  | .x => 762
  | .y => 508
  | .z => 1016

private def PreservesOutside (program : List LinearInstruction) (offset : Nat) (memory : Memory) : Prop :=
  ∀ address, address ≠ memory.registers 10 + BitVec.ofNat 256 offset →
    (executeLinear program memory).ram address = memory.ram address

private theorem retargetPreservesOutside {coefficients gates : Nat} (terms : List (GateTerm coefficients gates))
    (gate : Fin gates) (memory : Memory) : PreservesOutside (gateRetarget terms gate) (254 * gate.val) memory :=
  gateRetarget_outside terms gate memory

private theorem retargetProgramOutside (kind : RetargetKind) (memory : Memory) :
    PreservesOutside (retargetProgram kind) (retargetLowOffset kind) memory := by
  cases kind
  · exact retargetPreservesOutside curveTerms 2 memory
  · exact retargetPreservesOutside xTerms 3 memory
  · exact retargetPreservesOutside yTerms 2 memory
  · exact retargetPreservesOutside zTerms 4 memory

private theorem retargetCodeOutside (kind : RetargetKind) (memory : Memory) :
    PreservesOutside (retargetCode kind) (retargetLowOffset kind) memory := by
  rw [retargetCode_eq]
  exact retargetProgramOutside kind memory

/-- Each request program preserves every other RAM word. -/
theorem retargetCode_outside (kind : RetargetKind) (memory : Memory) (address : Word)
    (outside : address ≠ memory.registers 10 + BitVec.ofNat 256 (retargetLowOffset kind)) :
    (executeLinear (retargetCode kind) memory).ram address = memory.ram address :=
  retargetCodeOutside kind memory address outside

/-- The selected request preserves every word outside its single private write. -/
theorem retargetAt_outside (kind : RetargetKind) (sourceOffset : Nat) (targetBase : Register) (targetOffset : Nat)
    (memory : Memory) (notTen : targetBase ≠ 10) (notThirteen : targetBase ≠ 13) (address : Word)
    (outside : address ≠ memory.registers 11 + BitVec.ofNat 256 sourceOffset + BitVec.ofNat 256 (retargetLowOffset kind)) :
    (executeLinear (retargetAt kind sourceOffset targetBase targetOffset) memory).ram address = memory.ram address := by
  rw [retargetAt_memory kind sourceOffset targetBase targetOffset memory notTen notThirteen]
  apply retargetCode_outside
  simpa only [retargetAtPrepared, Function.update_of_ne (by decide : (10 : Register) ≠ 13), Function.update_self] using outside

end Kriterion.ArgoMAC.ArithmeticSimulator
