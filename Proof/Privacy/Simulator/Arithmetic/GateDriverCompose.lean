import Proof.Privacy.Simulator.Arithmetic.GateDriverTail

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A normal slot continues the gate. A cutoff slot returns at once. -/
noncomputable def gateDriverAfterSlot (next : Memory → PMF (Fin 1036 × Memory × Nat))
    (result : Fin 305 × Memory × Nat) : PMF (Fin 1036 × Memory × Nat) :=
  if result.1 = 300 then (next result.2.1).map fun tail => (tail.1, tail.2.1, result.2.2 + tail.2.2)
  else PMF.pure (1035, result.2.1, result.2.2)

/-- A checked slot composes with any proved normal continuation. -/
theorem gateDriverBlock_compose [BN254.FieldCertificate] (host : Machine) (attempts limit tailBudget budget : Nat)
    (gate : GateCode) (labels : Fin 1036 → Fin (host.size + 1))
    (present : ContainsGateDriver host attempts gate labels) (slot : Fin 3) (memory : Memory)
    (next : Memory → PMF (Fin 1036 × Memory × Nat))
    (attemptFits : attempts < 2 ^ 256) (ready : GateDriverSlotReady attempts limit gate slot memory)
    (enough : 8 + checkedSlotRunBudget attempts limit + tailBudget ≤ budget)
    (nextLaw : ∀ result ∈ (gateDriverSlotSamples attempts gate slot memory).support, result.1 = 300 →
      ∀ remaining, tailBudget ≤ remaining →
      run host remaining ⟨labels (gateDriverSlotLabels slot 300), result.2.1⟩ =
        (next result.2.1).bind fun tail =>
          (run host (remaining - tail.2.2) ⟨labels tail.1, tail.2.1⟩).map
            (Option.map fun final => (final.1, final.2 + tail.2.2))) :
    run host budget ⟨labels (gateDriverSlotLoadLabels slot 0), memory⟩ =
      ((gateDriverSlotSamples attempts gate slot memory).bind (gateDriverAfterSlot next)).bind fun result =>
        (run host (budget - result.2.2) ⟨labels result.1, result.2.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.2)) := by
  have enoughSlot : 8 + checkedSlotRunBudget attempts limit ≤ budget := by omega
  have execution := gateDriverBlock_slot host attempts limit (budget - (8 + checkedSlotRunBudget attempts limit))
    gate labels present slot memory attemptFits ready
  rw [Nat.add_sub_cancel' enoughSlot] at execution
  rw [execution, PMF.bind_bind]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  have bounded := gateDriverSlotSamples_cost attempts limit gate slot memory result attemptFits ready supported
  by_cases normal : result.1 = 300
  · simp only [gateDriverAfterSlot, if_pos normal, PMF.bind_map]
    rw [normal, nextLaw result supported normal (budget - result.2.2) (by omega), PMF.map_bind]
    apply congrArg (PMF.bind (next result.2.1))
    funext tail
    rw [Nat.sub_sub]
    simp only [PMF.map_comp, Option.map_map, Function.comp_def]
    apply congrArg (fun transform => PMF.map transform (run host (budget - (result.2.2 + tail.2.2))
      ⟨labels tail.1, tail.2.1⟩))
    funext outcome
    cases outcome <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · have cutoff : result.1 = 304 := bounded.2.resolve_left normal
    simp only [gateDriverAfterSlot, if_neg normal, PMF.pure_bind, cutoff]
    have returnLabel : gateDriverSlotLabels slot 304 = 1035 := by simp only [gateDriverSlotLabels, ↓reduceIte]
    rw [returnLabel]
    simp

end Kriterion.ArgoMAC.ArithmeticSimulator
