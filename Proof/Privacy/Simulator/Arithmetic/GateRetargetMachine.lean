import Proof.Privacy.Simulator.Arithmetic.GateRetarget
import Proof.Privacy.Simulator.Arithmetic.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The simulator has four fixed request forms. -/
inductive RetargetKind where
  | curve | x | y | z

/-- Each request form selects its complete fixed retarget program. -/
def retargetProgram : RetargetKind → List LinearInstruction
  | .curve => gateRetarget curveTerms 2
  | .x => gateRetarget xTerms 3
  | .y => gateRetarget yTerms 2
  | .z => gateRetarget zTerms 4

/-- Each program length includes every polynomial and retarget instruction. -/
def retargetLength : RetargetKind → Nat
  | .curve => 6395
  | .x => 5131
  | .y => 3853
  | .z => 6405

/-- The compiled source list has its exact declared length. -/
theorem retargetProgram_length (kind : RetargetKind) : (retargetProgram kind).length = retargetLength kind := by
  cases kind <;> simp [retargetProgram, retargetLength, gateRetarget_length,
    curvePolynomial_length, xPolynomial_length, yPolynomial_length, zPolynomial_length]

attribute [local irreducible] retargetProgram gateRetarget gatePolynomial polynomial

/-- The checked package keeps the fixed instruction lists symbolic. -/
private noncomputable def retargetCodePackage (kind : RetargetKind) :
    {program : List LinearInstruction // program = retargetProgram kind} := Classical.choice ⟨⟨retargetProgram kind, rfl⟩⟩

/-- The retarget code contains only the checked fixed instructions. -/
noncomputable def retargetCode (kind : RetargetKind) : List LinearInstruction := (retargetCodePackage kind).val

theorem retargetCode_eq (kind : RetargetKind) : retargetCode kind = retargetProgram kind :=
  (retargetCodePackage kind).property

theorem retargetCode_length (kind : RetargetKind) : (retargetCode kind).length = retargetLength kind := by
  rw [retargetCode_eq, retargetProgram_length]

theorem retargetCode_fits (kind : RetargetKind) : (retargetCode kind).length < 2 ^ 256 := by
  rw [retargetCode_length]
  cases kind <;> decide

/-- The standalone machine adds exactly one halt to the compiled request program. -/
noncomputable def retargetMachine (kind : RetargetKind) : Machine := linearMachine (retargetCode kind) (retargetCode_fits kind)

/-- The host returns the exact compiled retarget memory and charges every emitted instruction. -/
theorem retargetHost_continue [BN254.FieldCertificate] (kind : RetargetKind) (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host (retargetCode kind) labels)
    (base : Memory) (fuel : Nat) :
    run host (retargetLength kind + fuel) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels (retargetLength kind), executeLinear (retargetCode kind) base⟩).map
        (Option.map fun result => (result.1, result.2 + retargetLength kind)) := by
  simpa only [retargetCode_length] using linear_continue host (retargetCode kind) labels present base fuel

/-- The standalone retarget machine includes its instruction table and final halt. -/
theorem retargetMachine_budget (kind : RetargetKind) :
    (retargetMachine kind).size + 1 + ((retargetCode kind).length + 1) ≤ 12812 := by
  change (retargetCode kind).length + 1 + ((retargetCode kind).length + 1) ≤ 12812
  rw [retargetCode_length]
  cases kind <;> decide

end Kriterion.ArgoMAC.ArithmeticSimulator
