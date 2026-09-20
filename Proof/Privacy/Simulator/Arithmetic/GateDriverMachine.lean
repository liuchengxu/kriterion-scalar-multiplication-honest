import Proof.Privacy.Simulator.Arithmetic.GateDriverCost

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] gateDriverSamples

/-- The standalone gate contains each instruction before its two returns. -/
theorem gateDriver_self (attempts : Nat) (gate : GateCode) :
    ContainsGateDriver (gateDriver attempts gate) attempts gate id := by
  intro pc normal cutoff
  change (gateDriver attempts gate).code[pc.val] = relocate id ((gateDriver attempts gate).code[pc.val])
  generalize (gateDriver attempts gate).code[pc.val] = instruction
  cases instruction <;> rfl

/-- Both standalone return labels halt in one charged instruction. -/
theorem gateDriver_return [BN254.FieldCertificate] (attempts fuel : Nat) (gate : GateCode)
    (pc : Fin 1036) (memory : Memory) (terminal : pc = 1034 ∨ pc = 1035) :
    run (gateDriver attempts gate) (fuel + 1) ⟨pc, memory⟩ = PMF.pure (some (⟨pc, memory⟩, 1)) := by
  rcases terminal with rfl | rfl <;> simp [run, step, gateDriver]

/-- A host with halting return labels closes the checked source law. -/
theorem gateDriverBlock_halt [BN254.FieldCertificate] (host : Machine) (attempts limit : Nat)
    (gate : GateCode) (labels : Fin 1036 → Fin (host.size + 1))
    (present : ContainsGateDriver host attempts gate labels) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (ready : GateDriverReady attempts limit gate memory)
    (halts : ∀ pc, pc = 1034 ∨ pc = 1035 → host.code[(labels pc).val] = .halt) :
    run host (gateDriverRunBudget attempts limit + 1) ⟨labels 0, memory⟩ =
      (gateDriverSamples attempts gate memory).map fun result =>
        some (⟨labels result.1, result.2.1⟩, result.2.2 + 1) := by
  rw [gateDriverBlock_continue host attempts limit (gateDriverRunBudget attempts limit + 1)
    gate labels present memory attemptFits ready (by omega)]
  conv_rhs => rw [← PMF.bind_pure_comp]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  have bound := gateDriverSamples_cost attempts limit gate memory attemptFits ready result supported
  rw [show gateDriverRunBudget attempts limit + 1 - result.2.2 =
    (gateDriverRunBudget attempts limit - result.2.2) + 1 by omega, run]
  simp [step, halts result.1 bound.2, PMF.pure_map, Nat.add_comm]

end Kriterion.ArgoMAC.ArithmeticSimulator
