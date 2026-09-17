import Proof.Privacy.Source.FullGateGhostMass
import Proof.Privacy.Bounds.AdaptiveArithmetic
import Proof.Privacy.Transcript.EncPRFTranscript
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
attribute [local instance] fixedQueryDomainFintype residualFixedQueryDomainFintype instFintypeEncQueryDomainOfBlock

/-- One fixed bucket contains at most all recorded domains. -/
theorem fixedQueryDomain_card_le_length [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block)) (index : Pipeline.FixedKeyIndex) :
    Fintype.card (FixedQueryDomain history index) ≤ history.length := by
  classical
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ index)).trans (fixedQueryDomain_sum_card_le history)

/-- Membership equality transfers the exact prior query count. -/
theorem fixedQueryDomain_card_le_external [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (before : List (Sigma Garbling.oracleSpec.Answer))
    (members : ∀ record, record ∈ history ↔ record ∈ fixedOracleTranscriptRecords before)
    (index : Pipeline.FixedKeyIndex) :
    Fintype.card (FixedQueryDomain history index) ≤ before.length := by
  classical
  let embed : FixedQueryDomain history index → FixedQueryDomain (fixedOracleTranscriptRecords before) index :=
    fun query => ⟨query.1, by
      obtain ⟨record, member, same, domain⟩ := query.2
      exact ⟨record, (members record).mp member, same, domain⟩⟩
  have injective : Function.Injective embed := fun first second same =>
    Subtype.ext (congrArg (fun query : FixedQueryDomain (fixedOracleTranscriptRecords before) index => query.1) same)
  exact (Fintype.card_le_of_injective embed injective).trans
    ((fixedQueryDomain_card_le_length _ index).trans (fixedOracleTranscriptRecords_length_le before))

/-- Every residual bucket contains at most the external transcript length. -/
theorem residualFixedQueryDomain_card_le_external [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) (covered : Pipeline.FixedKeyIndex → Set Block)
    (index : Pipeline.FixedKeyIndex) :
    Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords transcript) covered index) ≤
      transcript.length := by
  exact (Fintype.card_le_of_injective
    (fun query : ResidualFixedQueryDomain (fixedOracleTranscriptRecords transcript) covered index => query.1)
    Subtype.val_injective).trans
    ((fixedQueryDomain_card_le_length _ index).trans (fixedOracleTranscriptRecords_length_le transcript))

/-- Every small prefix budget fits the actual fixed bucket count. -/
theorem sourcePriorCapacity [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (state : SimulatorState) (before : List (Sigma Garbling.oracleSpec.Answer))
    (members : ∀ record, record ∈ state.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords before)
    (queries : Nat) (small : queries < 2 ^ 100) (lengthBound : before.length ≤ queries)
    (index : Pipeline.FixedKeyIndex) :
    circuitBucketSize index + Fintype.card (FixedQueryDomain state.fixedTranscript index) ≤ Fintype.card Block := by
  have count := fixedQueryDomain_card_le_external state.fixedTranscript before members index
  have slots := circuitBucketSize_le index
  have capacity := smallBudget_slots_fit queries small
  omega

/-- Every small transcript budget fits all actual covered-domain choices. -/
theorem sourceResidualCapacity [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) (covered : Pipeline.FixedKeyIndex → Set Block)
    (queries : Nat) (small : queries < 2 ^ 100) (lengthBound : transcript.length ≤ queries)
    (index : Pipeline.FixedKeyIndex) :
    circuitBucketSize index +
      Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords transcript) covered index) ≤
        Fintype.card Block := by
  have count := residualFixedQueryDomain_card_le_external transcript covered index
  have slots := circuitBucketSize_le index
  have capacity := smallBudget_slots_fit queries small
  omega

/-- Every small transcript budget fits both linking equations and the EncPRF queries. -/
theorem sourceEncCapacity [Fintype Block]
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (queries : Nat) (small : queries < 2 ^ 100) (lengthBound : transcript.length ≤ queries)
    (index : EncPRF.PermutationIndex) :
    2 + Fintype.card (EncQueryDomain (encOracleTranscriptRecords transcript) index) ≤ Fintype.card Block := by
  classical
  have count : Fintype.card (EncQueryDomain (encOracleTranscriptRecords transcript) index) ≤ transcript.length :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)).trans
      (encExternalQueryCount_le transcript)
  have capacity := smallBudget_slots_fit queries small
  omega

/-- The actual source choice records exactly its fixed prefix queries. -/
theorem gateSourceChoose_historyMembers {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (member : selected ∈ (gateSourceChoose adversary parameter auxiliary table data).support)
    (record : PermutationRecord Pipeline.FixedKeyIndex Block) :
    record ∈ selected.2.2.1.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords selected.2.2.2 := by
  simp only [gateSourceChoose, PMF.mem_support_map_iff] at member
  obtain ⟨output, member, rfl⟩ := member
  rw [runTranscript_finalState idealOracleHandler _ _ output member]
  exact idealTranscriptFinal_fixedHistory_members (initialSourceOracle data) output.2.2
    (runOracleProgramWithTranscript_compatible idealOracleHandler _ _ output member) rfl record

/-- Every supported full source prefix fits the small work budget. -/
theorem fullGatePrefix_capacity [FieldCertificate] [GroupCertificate]
    [Fintype Block] [Fintype Pipeline.FixedKeyIndex] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : ScalarField) (witness : Garbling.Randomness)
    (sample : FullGatePrefixCoin adversary.State)
    (member : sample ∈ (fullGatePrefixSamples scalar witness parameter
      (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2)).support)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100)
    (index : Pipeline.FixedKeyIndex) :
    circuitBucketSize index + Fintype.card (FixedQueryDomain sample.2.2.2.2.1.fixedTranscript index) ≤
      Fintype.card Block := by
  simp only [fullGatePrefixSamples, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at member
  obtain ⟨randomness, _, tag, _, selected, member, rfl⟩ := member
  apply sourcePriorCapacity _ selected.2.2.2
    (gateSourceChoose_historyMembers adversary parameter auxiliary _ _ selected member) _ small
  exact (gateSourceChoose_length_le adversary parameter auxiliary _ _ selected member).trans
    (Nat.le_add_right _ _)


/-- The supported full source supplies every fixed and EncPRF capacity premise. -/
theorem fullGateSource_capacities [FieldCertificate] [GroupCertificate]
    [Fintype Block] [Fintype Pipeline.FixedKeyIndex] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : ScalarField) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State))
    (fallbackLength : ∀ retained source output, output ∈ (fallback retained source).support →
      (output.2.2.1 ++ output.2.2.2.2.2).length ≤
        adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter)
    (sample : FullGatePrefixCoin adversary.State)
    (sampleMember : sample ∈ (fullGatePrefixSamples scalar witness parameter
      (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2)).support)
    (output : FullGateTranscript adversary.State)
    (outputMember : output ∈ (fullGatePrefixKernel scalar
      (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
      fallback sample).support)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100) :
    (∀ index, circuitBucketSize index +
      Fintype.card (FixedQueryDomain sample.2.2.2.2.1.fixedTranscript index) ≤ Fintype.card Block) ∧
    (∀ (covered : Pipeline.FixedKeyIndex → Set Block) index, circuitBucketSize index +
      Fintype.card (ResidualFixedQueryDomain
        (fixedOracleTranscriptRecords (output.2.2.1 ++ output.2.2.2.2.2)) covered index) ≤ Fintype.card Block) ∧
    (∀ index, 2 + Fintype.card (EncQueryDomain
      (encOracleTranscriptRecords (output.2.2.1 ++ output.2.2.2.2.2)) index) ≤ Fintype.card Block) := by
  have lengthBound := fullGatePrefixKernel_length_le adversary parameter auxiliary scalar witness
    fallback fallbackLength sample sampleMember output outputMember
  refine ⟨fullGatePrefix_capacity adversary parameter auxiliary scalar witness sample sampleMember small, ?_, ?_⟩
  · intro covered index
    exact sourceResidualCapacity _ covered _ small lengthBound index
  · exact sourceEncCapacity _ _ small lengthBound

end
end Kriterion.ArgoMAC.Security
