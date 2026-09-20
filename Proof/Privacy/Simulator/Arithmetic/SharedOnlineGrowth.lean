import Proof.Privacy.Simulator.Arithmetic.EncLinkSourceGrowth
import Proof.Privacy.Simulator.Arithmetic.SharedOnlineCutoffSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Security Security.SharedSimulatorMachine
noncomputable section
attribute [local irreducible] sharedSourceCutoff sharedCommandListCutoff

/-- Every accepted online source fits the internal query reserve and uses at most one hash entry. -/
theorem sharedOnlineTotalProgram_growth [FieldCertificate] [GroupCertificate]
    (attempts limit : Nat) (frame : Shared.Simulator.State) (input : AffineInput) (output : Option Point)
    (state next : SharedOracleSource) (labels : Garbling.Labels)
    (bounded : SharedSourceCounts state limit) (hashBound : state.family.hash.length ≤ limit)
    (member : some (labels, next) ∈ (runSampledCutoff (sharedSourceCutoff attempts)
      (sharedOnlineTotalProgram attempts frame input output) state).support) :
    SharedSourceCounts next (limit + 836423) ∧ next.family.hash.length ≤ limit + 1 := by
  cases output with
  | none =>
    rw [sharedOnlineTotalProgram_none] at member
    obtain ⟨raw, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    cases raw with
    | none => simp at same
    | some raw =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at same
      have stateEq := same.2
      subst next
      have growth := sharedCommandListCutoff_growth attempts limit _ state raw.2 bounded reached
      have size := scheduleCommands_length ((frame.selectedCurve input).schedule input (frame.labels input).inputMac)
      rw [CurveGateRequest.schedule_length] at size
      change _ ≤ 3 * (5 * 254) at size
      refine ⟨growth.1.mono ?_, ?_⟩
      · simp only [List.length_map]
        omega
      · rw [growth.2]
        omega
  | some output =>
    rw [sharedOnlineTotalProgram_some] at member
    obtain ⟨coin, _, accepted⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    obtain ⟨linked, linkMember, programmed⟩ := (mem_support_bindCutoff _ _ _).mp accepted
    have link := sharedLinkProgram_growth attempts limit state linked.2 (frame.selectedCurve input)
      input (frame.labels input).inputMac linked.1 bounded linkMember
    obtain ⟨raw, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp programmed
    cases raw with
    | none => simp at same
    | some raw =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at same
      have stateEq := same.2
      subst next
      have growth := sharedCommandListCutoff_growth attempts (limit + 508) _ linked.2 raw.2 link.1 reached
      have size := scheduleCommands_length (pipelineGateSchedule (frame.selectedCurve input)
        (frame.selectedPoints input output (Vector.ofFn coin.1) coin.2) input (frame.labels input).inputMac linked.1)
      rw [pipelineGateSchedule_length_value] at size
      refine ⟨growth.1.mono ?_, ?_⟩
      · simp only [List.length_map]
        omega
      · rw [growth.2]
        omega

end
end Kriterion.ArgoMAC.ArithmeticSimulator
