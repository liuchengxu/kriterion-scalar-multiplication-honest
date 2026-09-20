import Proof.Privacy.Simulator.Arithmetic.GateDriverBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A slot and its normal continuation add their exact costs. -/
theorem gateDriverAfterSlot_cost (next : Memory → PMF (Fin 1036 × Memory × Nat))
    (head : Fin 305 × Memory × Nat) (headBudget tailBudget : Nat)
    (headBound : head.2.2 ≤ headBudget)
    (nextBound : head.1 = 300 → ∀ tail ∈ (next head.2.1).support,
      tail.2.2 ≤ tailBudget ∧ (tail.1 = 1034 ∨ tail.1 = 1035))
    (result : Fin 1036 × Memory × Nat) (supported : result ∈ (gateDriverAfterSlot next head).support) :
    result.2.2 ≤ headBudget + tailBudget ∧ (result.1 = 1034 ∨ result.1 = 1035) := by
  by_cases normal : head.1 = 300
  · simp only [gateDriverAfterSlot, if_pos normal] at supported
    obtain ⟨tail, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    have bound := nextBound normal tail member
    exact ⟨Nat.add_le_add headBound bound.1, bound.2⟩
  · simp only [gateDriverAfterSlot, if_neg normal] at supported
    have same : result = (1035, head.2.1, head.2.2) := by
      simpa only [PMF.support_pure, Set.mem_singleton_iff] using supported
    subst result
    exact ⟨le_trans headBound (Nat.le_add_right _ _), Or.inr rfl⟩

theorem gateRestoreSamples_cost (memory : Memory) (result : Fin 1036 × Memory × Nat)
    (supported : result ∈ (gateRestoreSamples memory).support) :
    result.2.2 ≤ 10 ∧ (result.1 = 1034 ∨ result.1 = 1035) := by
  have same : result = (1034, executeLinear gateDirectiveRestore memory, 10) := by
    simpa only [gateRestoreSamples, PMF.support_pure, Set.mem_singleton_iff] using supported
  subst result
  exact ⟨le_rfl, Or.inl rfl⟩

theorem gateThirdSamples_cost [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (ready : GateDriverSlotReady attempts limit gate 2 memory)
    (result : Fin 1036 × Memory × Nat) (supported : result ∈ (gateThirdSamples attempts gate memory).support) :
    result.2.2 ≤ gateSlotBudget attempts limit + 10 ∧ (result.1 = 1034 ∨ result.1 = 1035) := by
  obtain ⟨head, member, tail⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  exact gateDriverAfterSlot_cost gateRestoreSamples head (gateSlotBudget attempts limit) 10
    (gateDriverSlotSamples_cost attempts limit gate 2 memory head attemptFits ready member).1
    (fun _ => gateRestoreSamples_cost head.2.1) result tail

theorem gateTestSamples_cost [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (ready : GateTestReady attempts limit gate memory)
    (result : Fin 1036 × Memory × Nat) (supported : result ∈ (gateTestSamples attempts gate memory).support) :
    result.2.2 ≤ gateSlotBudget attempts limit + 15 ∧ (result.1 = 1034 ∨ result.1 = 1035) := by
  obtain ⟨tail, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  by_cases third : (executeLinear gateDriverTest memory).registers 1 = 0
  · simp only [if_pos third] at member
    have bound := gateThirdSamples_cost attempts limit gate _ attemptFits (ready third) tail member
    exact ⟨by dsimp; omega, bound.2⟩
  · simp only [if_neg third] at member
    have bound := gateRestoreSamples_cost _ tail member
    exact ⟨by dsimp; omega, bound.2⟩

theorem gateSecondSamples_cost [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (ready : GateSecondReady attempts limit gate memory)
    (result : Fin 1036 × Memory × Nat) (supported : result ∈ (gateSecondSamples attempts gate memory).support) :
    result.2.2 ≤ 2 * gateSlotBudget attempts limit + 15 ∧ (result.1 = 1034 ∨ result.1 = 1035) := by
  obtain ⟨head, member, tail⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  have bound := gateDriverAfterSlot_cost (gateTestSamples attempts gate) head (gateSlotBudget attempts limit)
    (gateSlotBudget attempts limit + 15)
    (gateDriverSlotSamples_cost attempts limit gate 1 memory head attemptFits ready.1 member).1
    (fun normal => gateTestSamples_cost attempts limit gate head.2.1 attemptFits (ready.2 head member normal)) result tail
  exact ⟨by omega, bound.2⟩

theorem gateBodySamples_cost [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (ready : GateBodyReady attempts limit gate memory)
    (result : Fin 1036 × Memory × Nat) (supported : result ∈ (gateBodySamples attempts gate memory).support) :
    result.2.2 ≤ 3 * gateSlotBudget attempts limit + 15 ∧ (result.1 = 1034 ∨ result.1 = 1035) := by
  obtain ⟨head, member, tail⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  have bound := gateDriverAfterSlot_cost (gateSecondSamples attempts gate) head (gateSlotBudget attempts limit)
    (2 * gateSlotBudget attempts limit + 15)
    (gateDriverSlotSamples_cost attempts limit gate 0 memory head attemptFits ready.1 member).1
    (fun normal => gateSecondSamples_cost attempts limit gate head.2.1 attemptFits (ready.2 head member normal)) result tail
  exact ⟨by omega, bound.2⟩

/-- Every complete gate sample fits the fixed reserve and has a valid return label. -/
theorem gateDriverSamples_cost [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (ready : GateDriverReady attempts limit gate memory)
    (result : Fin 1036 × Memory × Nat) (supported : result ∈ (gateDriverSamples attempts gate memory).support) :
    result.2.2 ≤ gateDriverRunBudget attempts limit ∧ (result.1 = 1034 ∨ result.1 = 1035) := by
  obtain ⟨tail, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have bound := gateBodySamples_cost attempts limit gate _ attemptFits ready tail member
  have prepared := gateDriverPrefixCost_bound gate memory
  refine ⟨?_, bound.2⟩
  change gateDriverPrefixCost gate memory + tail.2.2 ≤ gateDriverRunBudget attempts limit
  unfold gateDriverRunBudget
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
