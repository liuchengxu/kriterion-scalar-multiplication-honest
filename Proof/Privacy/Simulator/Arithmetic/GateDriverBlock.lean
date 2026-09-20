import Proof.Privacy.Simulator.Arithmetic.GateDriverSuffix

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The complete gate returns its exact checked source law within a fixed instruction reserve. -/
theorem gateDriverBlock_continue [BN254.FieldCertificate] (host : Machine) (attempts limit budget : Nat)
    (gate : GateCode) (labels : Fin 1036 → Fin (host.size + 1))
    (present : ContainsGateDriver host attempts gate labels) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (ready : GateDriverReady attempts limit gate memory)
    (enough : gateDriverRunBudget attempts limit ≤ budget) :
    run host budget ⟨labels 0, memory⟩ =
      (gateDriverSamples attempts gate memory).bind fun result =>
        (run host (budget - result.2.2) ⟨labels result.1, result.2.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.2)) := by
  have prefixBound := gateDriverPrefixCost_bound gate memory
  have prefixEnough : gateDriverPrefixCost gate memory ≤ budget := by unfold gateDriverRunBudget at enough; omega
  have executed := gateDriverBlock_prefix host attempts gate labels present memory (budget - gateDriverPrefixCost gate memory)
  rw [Nat.add_sub_cancel' prefixEnough] at executed
  rw [executed, gateBodySamples_continue host attempts limit (budget - gateDriverPrefixCost gate memory)
    gate labels present _ attemptFits ready (by unfold gateDriverRunBudget at enough; omega)]
  simp only [gateDriverSamples, PMF.bind_map]
  have shifted := checkedSource_shiftCharge (gateBodySamples attempts gate (gateDriverPrepared gate memory))
    (fun result => result.2.2) (fun result remaining => run host remaining ⟨labels result.1, result.2.1⟩)
    (budget - gateDriverPrefixCost gate memory) (gateDriverPrefixCost gate memory)
  simpa only [Function.comp_def, Nat.add_sub_cancel' prefixEnough] using shifted

/-- The gate budget charges its table, all executed instructions, and the final halt. -/
theorem gateDriver_budget (attempts limit : Nat) (gate : GateCode) :
    (gateDriver attempts gate).size + 1 + (gateDriverRunBudget attempts limit + 1) =
      7722 * attempts + 168 * limit + 1763 := by
  change 1035 + 1 + (gateDriverRunBudget attempts limit + 1) = _
  unfold gateDriverRunBudget gateSlotBudget checkedSlotRunBudget
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
