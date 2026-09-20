import Proof.Privacy.Simulator.Arithmetic.GateDriverSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The restore source has the exact host return law. -/
theorem gateRestoreSamples_continue [BN254.FieldCertificate] (host : Machine) (attempts budget : Nat)
    (gate : GateCode) (labels : Fin 1036 → Fin (host.size + 1))
    (present : ContainsGateDriver host attempts gate labels) (memory : Memory) (enough : 10 ≤ budget) :
    run host budget ⟨labels 1024, memory⟩ =
      (gateRestoreSamples memory).bind fun result =>
        (run host (budget - result.2.2) ⟨labels result.1, result.2.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.2)) := by
  simpa only [gateRestoreSamples, PMF.pure_bind, Nat.add_sub_cancel' enough] using
    gateDriverBlock_restore_return host attempts (budget - 10) gate labels present memory

/-- The third slot returns through the normal restore or the cutoff exit. -/
theorem gateThirdSamples_continue [BN254.FieldCertificate] (host : Machine) (attempts limit budget : Nat)
    (gate : GateCode) (labels : Fin 1036 → Fin (host.size + 1))
    (present : ContainsGateDriver host attempts gate labels) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (ready : GateDriverSlotReady attempts limit gate 2 memory)
    (enough : gateSlotBudget attempts limit + 10 ≤ budget) :
    run host budget ⟨labels 711, memory⟩ =
      (gateThirdSamples attempts gate memory).bind fun result =>
        (run host (budget - result.2.2) ⟨labels result.1, result.2.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.2)) := by
  apply gateDriverBlock_compose host attempts limit 10 budget gate labels present 2 memory
    gateRestoreSamples attemptFits ready enough
  intro result _ _ remaining bound
  exact gateRestoreSamples_continue host attempts remaining gate labels present result.2.1 bound

/-- The count branch includes the third slot only when the saved count requires it. -/
theorem gateTestSamples_continue [BN254.FieldCertificate] (host : Machine) (attempts limit budget : Nat)
    (gate : GateCode) (labels : Fin 1036 → Fin (host.size + 1))
    (present : ContainsGateDriver host attempts gate labels) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (ready : GateTestReady attempts limit gate memory)
    (enough : gateSlotBudget attempts limit + 15 ≤ budget) :
    run host budget ⟨labels 706, memory⟩ =
      (gateTestSamples attempts gate memory).bind fun result =>
        (run host (budget - result.2.2) ⟨labels result.1, result.2.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.2)) := by
  have executed := gateDriverBlock_test_return host attempts (budget - 5) gate labels present memory
  rw [Nat.add_sub_cancel' (by omega : 5 ≤ budget)] at executed
  rw [executed]
  simp only [gateTestSamples, PMF.bind_map]
  by_cases third : (executeLinear gateDriverTest memory).registers 1 = 0
  · simp only [if_pos third]
    rw [gateThirdSamples_continue host attempts limit (budget - 5) gate labels present _ attemptFits
      (ready third) (by omega)]
    have shifted := checkedSource_shiftCharge (gateThirdSamples attempts gate (executeLinear gateDriverTest memory))
      (fun result => result.2.2) (fun result remaining => run host remaining ⟨labels result.1, result.2.1⟩)
      (budget - 5) 5
    simpa only [Function.comp_def, Nat.add_sub_cancel' (by omega : 5 ≤ budget)] using shifted
  · simp only [if_neg third]
    rw [gateRestoreSamples_continue host attempts (budget - 5) gate labels present _ (by omega)]
    have shifted := checkedSource_shiftCharge (gateRestoreSamples (executeLinear gateDriverTest memory))
      (fun result => result.2.2) (fun result remaining => run host remaining ⟨labels result.1, result.2.1⟩)
      (budget - 5) 5
    simpa only [Function.comp_def, Nat.add_sub_cancel' (by omega : 5 ≤ budget)] using shifted

/-- The second slot continues through the count branch after a normal return. -/
theorem gateSecondSamples_continue [BN254.FieldCertificate] (host : Machine) (attempts limit budget : Nat)
    (gate : GateCode) (labels : Fin 1036 → Fin (host.size + 1))
    (present : ContainsGateDriver host attempts gate labels) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (ready : GateSecondReady attempts limit gate memory)
    (enough : 2 * gateSlotBudget attempts limit + 15 ≤ budget) :
    run host budget ⟨labels 393, memory⟩ =
      (gateSecondSamples attempts gate memory).bind fun result =>
        (run host (budget - result.2.2) ⟨labels result.1, result.2.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.2)) := by
  apply gateDriverBlock_compose host attempts limit (gateSlotBudget attempts limit + 15) budget gate labels present 1 memory
    (gateTestSamples attempts gate) attemptFits ready.1 (by unfold gateSlotBudget at enough ⊢; omega)
  intro result supported normal remaining bound
  exact gateTestSamples_continue host attempts limit remaining gate labels present result.2.1 attemptFits
    (ready.2 result supported normal) bound

/-- The first slot continues through the complete remaining gate after a normal return. -/
theorem gateBodySamples_continue [BN254.FieldCertificate] (host : Machine) (attempts limit budget : Nat)
    (gate : GateCode) (labels : Fin 1036 → Fin (host.size + 1))
    (present : ContainsGateDriver host attempts gate labels) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (ready : GateBodyReady attempts limit gate memory)
    (enough : 3 * gateSlotBudget attempts limit + 15 ≤ budget) :
    run host budget ⟨labels 80, memory⟩ =
      (gateBodySamples attempts gate memory).bind fun result =>
        (run host (budget - result.2.2) ⟨labels result.1, result.2.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.2)) := by
  apply gateDriverBlock_compose host attempts limit (2 * gateSlotBudget attempts limit + 15) budget gate labels present 0 memory
    (gateSecondSamples attempts gate) attemptFits ready.1 (by unfold gateSlotBudget at enough ⊢; omega)
  intro result supported normal remaining bound
  exact gateSecondSamples_continue host attempts limit remaining gate labels present result.2.1 attemptFits
    (ready.2 result supported normal) bound

end Kriterion.ArgoMAC.ArithmeticSimulator
