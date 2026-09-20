import Proof.Privacy.Simulator.Arithmetic.GateDriverPrefix
import Proof.Privacy.Simulator.Arithmetic.GateDriverSlot

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The slot-count branch tests the saved count against three. -/
theorem gateDriverTest_value (memory : Memory) :
    (executeLinear gateDriverTest memory).registers 1 = memory.ram 20 ^^^ 3 := by
  simp [gateDriverTest, executeLinear, LinearInstruction.execute, Arithmetic.eval]

/-- The normal return restores the five saved caller registers. -/
theorem gateDriverBlock_restore_return [BN254.FieldCertificate] (host : Machine) (attempts fuel : Nat)
    (gate : GateCode) (labels : Fin 1036 → Fin (host.size + 1))
    (present : ContainsGateDriver host attempts gate labels) (memory : Memory) :
    run host (10 + fuel) ⟨labels 1024, memory⟩ =
      (run host fuel ⟨labels 1034, executeLinear gateDirectiveRestore memory⟩).map
        (Option.map fun result => (result.1, result.2 + 10)) := by
  exact linear_continue host gateDirectiveRestore (labels ∘ gateDriverRestoreLabels)
    (gateDriverBlock_restore host attempts gate labels present) memory fuel

/-- The test executes the third slot exactly when the saved count is three. -/
theorem gateDriverBlock_test_return [BN254.FieldCertificate] (host : Machine) (attempts fuel : Nat)
    (gate : GateCode) (labels : Fin 1036 → Fin (host.size + 1))
    (present : ContainsGateDriver host attempts gate labels) (memory : Memory) :
    run host (5 + fuel) ⟨labels 706, memory⟩ =
      (run host fuel ⟨labels (if (executeLinear gateDriverTest memory).registers 1 = 0 then 711 else 1024),
        executeLinear gateDriverTest memory⟩).map
        (Option.map fun result => (result.1, result.2 + 5)) := by
  have test := linear_continue host gateDriverTest (labels ∘ gateDriverTestLabels)
    (gateDriverBlock_test host attempts gate labels present) memory (fuel + 1)
  change run host (4 + (fuel + 1)) ⟨labels 706, memory⟩ = _ at test
  have branch : host.code[(labels 710).val] = .branch 1 (labels 711) (labels 1024) := by
    simpa [gateDriver, relocate] using present 710 (by decide) (by decide)
  rw [show 5 + fuel = 4 + (fuel + 1) by omega, test]
  change ((run host (fuel + 1) ⟨labels 710, executeLinear gateDriverTest memory⟩).map _) = _
  rw [run]
  simp only [step, branch, show gateDriverTest.length = 4 from rfl]
  split <;> simp_all [PMF.pure_bind, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

end Kriterion.ArgoMAC.ArithmeticSimulator
