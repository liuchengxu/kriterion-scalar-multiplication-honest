import Proof.Privacy.Simulator.Arithmetic.GateDriverSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
noncomputable section

/-- Each composed slot returns through the normal gate exit or the cutoff gate exit. -/
theorem gateDriverAfterSlot_returns (source : PMF (Fin 305 × Memory × Nat))
    (next : Memory → PMF (Fin 1036 × Memory × Nat))
    (returns : ∀ memory result, result ∈ (next memory).support → result.1 = 1034 ∨ result.1 = 1035)
    (result : Fin 1036 × Memory × Nat) (supported : result ∈ (source.bind (gateDriverAfterSlot next)).support) :
    result.1 = 1034 ∨ result.1 = 1035 := by
  obtain ⟨head, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  unfold gateDriverAfterSlot at member
  split at member
  · obtain ⟨tail, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact returns head.2.1 tail reached
  · simp only [PMF.mem_support_pure_iff] at member
    subst result
    exact Or.inr rfl

/-- The normal restoration has only the normal gate exit. -/
theorem gateRestoreSamples_returns (memory : Memory) (result : Fin 1036 × Memory × Nat)
    (supported : result ∈ (gateRestoreSamples memory).support) : result.1 = 1034 ∨ result.1 = 1035 := by
  simp only [gateRestoreSamples, PMF.mem_support_pure_iff] at supported
  subst result
  exact Or.inl rfl

/-- The complete gate source has only the two declared return labels. -/
theorem gateDriverSamples_returns (attempts : Nat) (gate : GateCode) (memory : Memory)
    (result : Fin 1036 × Memory × Nat) (supported : result ∈ (gateDriverSamples attempts gate memory).support) :
    result.1 = 1034 ∨ result.1 = 1035 := by
  have third : ∀ memory result, result ∈ (gateThirdSamples attempts gate memory).support → result.1 = 1034 ∨ result.1 = 1035 := by
    intro memory result supported
    exact gateDriverAfterSlot_returns _ gateRestoreSamples gateRestoreSamples_returns result supported
  have test : ∀ memory result, result ∈ (gateTestSamples attempts gate memory).support → result.1 = 1034 ∨ result.1 = 1035 := by
    intro memory result supported
    obtain ⟨tail, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    split at reached
    · exact third _ tail reached
    · exact gateRestoreSamples_returns _ tail reached
  have second : ∀ memory result, result ∈ (gateSecondSamples attempts gate memory).support → result.1 = 1034 ∨ result.1 = 1035 := by
    intro memory result supported
    exact gateDriverAfterSlot_returns _ (gateTestSamples attempts gate) test result supported
  obtain ⟨tail, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact gateDriverAfterSlot_returns _ (gateSecondSamples attempts gate) second tail reached

end
end Kriterion.ArgoMAC.ArithmeticSimulator
