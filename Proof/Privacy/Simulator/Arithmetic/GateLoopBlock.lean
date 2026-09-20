import Proof.Privacy.Simulator.Arithmetic.GateLoopSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The loop returns normally at the next boundary or stops at the shared cutoff exit. -/
def gateLoopReturn {count : Nat} (index : Nat) (within : index ≤ count) (success : Bool) :
    Fin (1036 * count + 2) :=
  if success then gateLoopBoundary index within else ⟨1036 * count + 1, by omega⟩

/-- The host executes a contiguous gate schedule with exact source cost. -/
theorem gateLoopBlock_continue [BN254.FieldCertificate] {count : Nat} (host : Machine)
    (plan : Vector GateCode count) (attempts limit : Nat) (fits : 1036 * count + 1 < 2 ^ 256)
    (labels : Fin (1036 * count + 2) → Fin (host.size + 1))
    (present : ContainsGateLoop host plan attempts fits labels) (remaining index fuel : Nat)
    (memory : Memory) (within : index + remaining ≤ count) (attemptFits : attempts < 2 ^ 256)
    (ready : GateLoopReady plan attempts limit remaining index memory) :
    run host (gateDriverRunBudget attempts limit * remaining + fuel)
      ⟨labels (gateLoopBoundary index (by omega)), memory⟩ =
      (gateLoopSamples plan attempts remaining index memory).bind fun result =>
        (run host (gateDriverRunBudget attempts limit * remaining + fuel - result.2.2)
          ⟨labels (gateLoopReturn (index + remaining) within result.1), result.2.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.2)) := by
  induction remaining generalizing index fuel memory with
  | zero =>
      simp only [gateLoopSamples, PMF.pure_bind, Nat.mul_zero, Nat.zero_add, Nat.add_zero,
        Nat.sub_zero, gateLoopReturn, ↓reduceIte]
      rw [show (Option.map fun final : Configuration (host.size + 1) × Nat => (final.1, final.2)) = id from by
        funext value; cases value <;> rfl, PMF.map_id]
  | succ remaining ih =>
      have inside : index < count := by omega
      let selected : Fin count := ⟨index, inside⟩
      simp only [GateLoopReady, dif_pos inside] at ready
      have executed := gateDriverBlock_continue host attempts limit
        (gateDriverRunBudget attempts limit * (remaining + 1) + fuel) plan[selected]
        (labels ∘ gateLoopLabels selected) (gateLoopBlock_contains host plan attempts fits labels present selected)
        memory attemptFits ready.1 (by rw [Nat.mul_succ]; omega)
      have entry : gateLoopLabels selected 0 = gateLoopBoundary index (by omega) := rfl
      change run host _ ⟨labels (gateLoopLabels selected 0), memory⟩ = _ at executed
      rw [entry] at executed
      rw [executed]
      conv_rhs => rw [gateLoopSamples, dif_pos inside, PMF.bind_bind]
      apply Security.ThreePhase.bind_eq_on_support
      intro result supported
      have bound := gateDriverSamples_cost attempts limit plan[selected] memory attemptFits ready.1 result supported
      by_cases normal : result.1 = 1034
      · simp only [if_pos normal, PMF.bind_map]
        have nextLabel : gateLoopLabels selected result.1 = gateLoopBoundary (index + 1) (by omega) := by
          rw [normal]; rfl
        change (run host _ ⟨labels (gateLoopLabels selected result.1), result.2.1⟩).map _ = _
        rw [nextLabel]
        have amount : gateDriverRunBudget attempts limit * (remaining + 1) + fuel - result.2.2 =
            gateDriverRunBudget attempts limit * remaining + (gateDriverRunBudget attempts limit + fuel - result.2.2) := by
          rw [Nat.mul_succ]; omega
        rw [amount, ih (index + 1) (gateDriverRunBudget attempts limit + fuel - result.2.2) result.2.1
          (by omega) (ready.2 result supported normal), PMF.map_bind]
        apply congrArg (PMF.bind (gateLoopSamples plan attempts remaining (index + 1) result.2.1))
        funext tail
        have remainingFuel : gateDriverRunBudget attempts limit * remaining +
            (gateDriverRunBudget attempts limit + fuel - result.2.2) - tail.2.2 =
            gateDriverRunBudget attempts limit * (remaining + 1) + fuel - (result.2.2 + tail.2.2) := by
          rw [Nat.mul_succ]; omega
        have returnLabel : gateLoopReturn (index + 1 + remaining) (by omega) tail.1 =
            gateLoopReturn (index + (remaining + 1)) within tail.1 := by
          congr 1 <;> omega
        rw [remainingFuel, returnLabel]
        simp only [PMF.map_comp, Option.map_map, Function.comp_def]
        apply congrArg (fun transform => PMF.map transform (run host
          (gateDriverRunBudget attempts limit * (remaining + 1) + fuel - (result.2.2 + tail.2.2))
          ⟨labels (gateLoopReturn (index + (remaining + 1)) within tail.1), tail.2.1⟩))
        funext outcome
        cases outcome <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · have cutoff : result.1 = 1035 := bound.2.resolve_left normal
        simp only [if_neg normal, PMF.pure_bind, gateLoopReturn, Bool.false_eq_true, ↓reduceIte]
        change (run host _ ⟨labels (gateLoopLabels selected result.1), result.2.1⟩).map _ = _
        rw [cutoff]
        rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
