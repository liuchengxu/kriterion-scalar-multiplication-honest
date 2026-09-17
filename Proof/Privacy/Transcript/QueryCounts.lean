import Proof.Privacy.Transcript.RealTranscriptMass
import Proof.Privacy.Distribution.HashQueryDistribution
import Proof.Privacy.Transcript.AdaptiveTranscript

namespace Kriterion.ArgoMAC.Security

open Cryptography

noncomputable section

local instance [Fintype Block]
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (index : Pipeline.FixedKeyIndex) : Fintype (FixedQueryDomain history index) := by
  classical
  unfold FixedQueryDomain
  infer_instance

/-- Each distinct queried domain uses at least one external record. -/
theorem fixedQueryDomain_sum_card_le [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block)) :
    (∑ index, Fintype.card (FixedQueryDomain history index)) ≤ history.length := by
  classical
  let pick : (index : Pipeline.FixedKeyIndex) → FixedQueryDomain history index →
      PermutationRecord Pipeline.FixedKeyIndex Block := fun _ query => Classical.choose query.2
  have picked (index) (query : FixedQueryDomain history index) :
      pick index query ∈ history ∧ (pick index query).index = index ∧
        (pick index query).domain = query.1 := Classical.choose_spec query.2
  let embed : (Σ index, FixedQueryDomain history index) → history.toFinset :=
    fun query => ⟨pick query.1 query.2, List.mem_toFinset.mpr (picked query.1 query.2).1⟩
  have injective : Function.Injective embed := by
    intro first second equal
    have record := congrArg Subtype.val equal
    have indices : first.1 = second.1 :=
      (picked first.1 first.2).2.1.symm.trans
        ((congrArg PermutationRecord.index record).trans (picked second.1 second.2).2.1)
    rcases first with ⟨index, first⟩
    rcases second with ⟨other, second⟩
    dsimp only at indices
    subst other
    apply congrArg (Sigma.mk index)
    apply Subtype.ext
    exact (picked index first).2.2.symm.trans
      ((congrArg PermutationRecord.domain record).trans (picked index second).2.2)
  calc
    _ = Fintype.card (Σ index, FixedQueryDomain history index) := Fintype.card_sigma.symm
    _ ≤ Fintype.card history.toFinset := Fintype.card_le_of_injective embed injective
    _ = history.toFinset.card := Fintype.card_coe _
    _ ≤ history.length := List.toFinset_card_le _

/-- The extraction retains at most one fixed-oracle record per external query. -/
theorem fixedOracleTranscriptRecords_length_le
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (fixedOracleTranscriptRecords transcript).length ≤ transcript.length := by
  induction transcript with
  | nil => exact Nat.le_refl _
  | cons entry rest ih =>
      rcases entry with ⟨query, answer⟩
      cases query <;> simp only [fixedOracleTranscriptRecords, List.length_cons] <;> omega

/-- All distinct fixed-oracle domains fit the external transcript length. -/
theorem fixedExternalQueryCount_le [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (∑ index, Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index)) ≤
      transcript.length :=
  (fixedQueryDomain_sum_card_le _).trans (fixedOracleTranscriptRecords_length_le transcript)

universe u uAux

variable {oracle : OracleSpec}
  {Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle Topology State : Type u}
  {Aux : Type uAux}
  (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle)
  (randomTape : Nat → PMF Randomness) (realOracle : OracleHandler oracle Randomness)
  (topology : Circuit → Topology)
  (simulator : GarbledCircuit.Simulator Input Output Public Labels Topology State)
  (idealOracle : OracleHandler oracle State)
  (adversary : GarbledCircuit.AdaptiveAdversary oracle Input Public Labels Aux)
  (parameter : Nat) (circuit : Circuit) (auxiliary : Aux)

/-- Every real adaptive transcript fits both declared query budgets. -/
theorem realAdaptiveTranscript_queryLength_le
    (transcript : AdaptiveTranscript oracle Input Public Labels)
    (member : transcript ∈
      (realAdaptiveTranscript scheme randomTape realOracle adversary parameter circuit auxiliary).support) :
    transcript.beforeEncode.length + transcript.afterEncode.length ≤
      adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter := by
  rw [realAdaptiveTranscript, PMF.mem_support_bind_iff] at member
  obtain ⟨randomness, _, member⟩ := member
  rw [PMF.mem_support_bind_iff] at member
  obtain ⟨selected, firstMember, member⟩ := member
  rw [PMF.mem_support_map_iff] at member
  obtain ⟨decided, secondMember, rfl⟩ := member
  exact Nat.add_le_add
    (runOracleProgramWithTranscript_length_le _ _ _ _ firstMember)
    (runOracleProgramWithTranscript_length_le _ _ _ _ secondMember)

/-- Every ideal adaptive transcript fits both declared query budgets. -/
theorem idealAdaptiveTranscript_queryLength_le
    (transcript : AdaptiveTranscript oracle Input Public Labels)
    (member : transcript ∈
      (idealAdaptiveTranscript scheme topology simulator idealOracle adversary parameter circuit auxiliary).support) :
    transcript.beforeEncode.length + transcript.afterEncode.length ≤
      adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter := by
  rw [idealAdaptiveTranscript, PMF.mem_support_bind_iff] at member
  obtain ⟨simulated, _, member⟩ := member
  rw [PMF.mem_support_bind_iff] at member
  obtain ⟨selected, firstMember, member⟩ := member
  rw [PMF.mem_support_bind_iff] at member
  obtain ⟨encoded, _, member⟩ := member
  rw [PMF.mem_support_map_iff] at member
  obtain ⟨decided, secondMember, rfl⟩ := member
  exact Nat.add_le_add
    (runOracleProgramWithTranscript_length_le _ _ _ _ firstMember)
    (runOracleProgramWithTranscript_length_le _ _ _ _ secondMember)

/-- Every scheduled gate selects two pad slots or three hash slots. -/
theorem gateScheduleActiveSlotCount_bounds (schedule : List GateDirective) :
    2 * schedule.length ≤ gateScheduleActiveSlotCount schedule ∧
      gateScheduleActiveSlotCount schedule ≤ 3 * schedule.length := by
  refine ⟨?_, gateScheduleActiveSlotCount_le schedule⟩
  induction schedule with
  | nil => simp [gateScheduleActiveSlotCount]
  | cons directive remaining ih =>
      cases bit : directive.bit <;>
        simp [gateScheduleActiveSlotCount, GateDirective.activeSlotCount, bit] at * <;> omega

/-- The complete circuit schedule has these fixed-permutation slot counts. -/
theorem pipelineGateSchedule_query_counts (curve : CurveGateRequest)
    (points : PointGateRequests) (input : BN254.AffineInput)
    (curveInputMac pointInputMac : InputMac) :
    let schedule := pipelineGateSchedule curve points input curveInputMac pointInputMac
    5 * schedule.length = 1393190 ∧
      557276 ≤ gateScheduleActiveSlotCount schedule ∧
      gateScheduleActiveSlotCount schedule ≤ 835914 := by
  dsimp only
  have bounds := gateScheduleActiveSlotCount_bounds
    (pipelineGateSchedule curve points input curveInputMac pointInputMac)
  rw [pipelineGateSchedule_length_value] at bounds ⊢
  exact ⟨by decide, bounds⟩

end

end Kriterion.ArgoMAC.Security
