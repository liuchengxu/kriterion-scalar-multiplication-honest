import Proof.Privacy.Source.FullGateSourceMass

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

/-- Both transcript segments use the same Enc and hash oracle constraints. -/
theorem nonFixedTranscriptCompatible_append (randomness : Garbling.Randomness)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) :
    NonFixedTranscriptCompatible randomness (before ++ after) ↔
      NonFixedTranscriptCompatible randomness before ∧ NonFixedTranscriptCompatible randomness after := by
  induction before with
  | nil => simp [NonFixedTranscriptCompatible]
  | cons entry tail inductionHypothesis =>
      rcases entry with ⟨request, answer⟩
      cases request <;> simp [NonFixedTranscriptCompatible, inductionHypothesis, and_assoc]

/-- The ideal transcript preserves both non-fixed oracle families. -/
theorem idealTranscriptFinal_oracles (state : SimulatorState)
    (history : List (Sigma Garbling.oracleSpec.Answer)) :
    (transcriptFinalState idealOracleHandler state history).encOracle = state.encOracle ∧
      (transcriptFinalState idealOracleHandler state history).hashOracle = state.hashOracle := by
  induction history generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons entry tail inductionHypothesis =>
      have result := inductionHypothesis (idealOracleHandler entry.1 state).2
      rcases entry with ⟨request, answer⟩
      cases request <;> exact result

/-- A compatible ideal transcript satisfies the actual Enc and hash constraints. -/
theorem idealTranscript_nonfixed (state : SimulatorState) (randomness : Garbling.Randomness)
    (history : List (Sigma Garbling.oracleSpec.Answer))
    (enc : state.encOracle = randomness.encPRFOracle) (hash : state.hashOracle = randomness.hashOracle)
    (compatible : OracleTranscriptCompatible idealOracleHandler state history) :
    NonFixedTranscriptCompatible randomness history := by
  have real := (idealOracleTranscriptCompatible_iff_real state
    {randomness with fixedKeyOracle := state.fixedOracle} history rfl enc hash).mp compatible
  rw [realOracleTranscriptCompatible_iff, nonFixedTranscriptCompatible_update] at real
  exact real.2

/-- The selected source prefix keeps the original Enc and hash oracle families. -/
theorem gateSourceChoose_oracles {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (member : selected ∈ (gateSourceChoose adversary parameter auxiliary table data).support) :
    selected.2.2.1.encOracle = data.encPRFOracle ∧ selected.2.2.1.hashOracle = data.hashOracle := by
  simp only [gateSourceChoose, PMF.mem_support_map_iff] at member
  obtain ⟨result, resultMember, rfl⟩ := member
  have final := runTranscript_finalState idealOracleHandler
    (adversary.chooseInput parameter table auxiliary) (initialSourceOracle data) result resultMember
  change result.2.1.encOracle = data.encPRFOracle ∧ result.2.1.hashOracle = data.hashOracle
  rw [final]
  exact idealTranscriptFinal_oracles (initialSourceOracle data) result.2.2


/-- Both supported source phases satisfy the actual Enc and hash transcript constraints. -/
theorem gateSourceObserve_nonfixed {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData) (randomness : Garbling.Randomness)
    (enc : data.encPRFOracle = randomness.encPRFOracle) (hash : data.hashOracle = randomness.hashOracle)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (selectedMember : selected ∈ (gateSourceChoose adversary parameter auxiliary table data).support)
    (view : SelectedGateView)
    (output : Pipeline.Table × (AffineInput × adversary.State) × List (Sigma Garbling.oracleSpec.Answer) ×
      Garbling.Labels × Bool × List (Sigma Garbling.oracleSpec.Answer))
    (member : output ∈ (gateSourceObserve adversary parameter auxiliary table selected view data).support) :
    NonFixedTranscriptCompatible randomness (output.2.2.1 ++ output.2.2.2.2.2) := by
  have first : NonFixedTranscriptCompatible randomness selected.2.2.2 := by
    simp only [gateSourceChoose, PMF.mem_support_map_iff] at selectedMember
    obtain ⟨result, resultMember, rfl⟩ := selectedMember
    exact idealTranscript_nonfixed (initialSourceOracle data) randomness result.2.2 enc hash
      (runOracleProgramWithTranscript_compatible idealOracleHandler
        (adversary.chooseInput parameter table auxiliary) (initialSourceOracle data) result resultMember)
  have oracles := gateSourceChoose_oracles adversary parameter auxiliary table data selected selectedMember
  simp only [gateSourceObserve, PMF.mem_support_map_iff] at member
  obtain ⟨result, resultMember, rfl⟩ := member
  apply nonFixedTranscriptCompatible_append randomness _ _ |>.mpr
  refine ⟨first, ?_⟩
  exact idealTranscript_nonfixed _ randomness result.2.2
    (by simpa only [programSelectedGateView, programGateSchedule_encOracle] using oracles.1.trans enc)
    (by simpa only [programSelectedGateView, programGateSchedule_hashOracle] using oracles.2.trans hash)
    (runOracleProgramWithTranscript_compatible idealOracleHandler
      (adversary.decide parameter table (sourceInputLabels data selected.1) auxiliary selected.2.1)
      (programSelectedGateView selected.2.2.1 selected.1 (sourceInputLabels data selected.1).inputMac view)
      result resultMember)


/-- A complete full-source continuation keeps the original non-fixed transcript constraints. -/
theorem fullGatePrefixKernel_nonfixed [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : ScalarField) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (Pipeline.Table × (AffineInput × adversary.State) × List (Sigma Garbling.oracleSpec.Answer) ×
        Garbling.Labels × Bool × List (Sigma Garbling.oracleSpec.Answer)))
    (sample : Garbling.Randomness × ((RawCircuitGate → FullHashLift) × CircuitMaskTables) ×
      (AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))))
    (sampleMember : sample ∈ (fullGatePrefixSamples scalar witness parameter
      (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2)).support)
    (complete : FullSourceComplete sample.2.1.1)
    (output : Pipeline.Table × (AffineInput × adversary.State) × List (Sigma Garbling.oracleSpec.Answer) ×
      Garbling.Labels × Bool × List (Sigma Garbling.oracleSpec.Answer))
    (member : output ∈ (fullGatePrefixKernel scalar
      (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
      fallback sample).support) :
    NonFixedTranscriptCompatible sample.1 (output.2.2.1 ++ output.2.2.2.2.2) := by
  classical
  simp only [fullGatePrefixSamples, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at sampleMember
  obtain ⟨randomness, _, tag, _, selected, selectedMember, rfl⟩ := sampleMember
  simp only [fullGatePrefixKernel, complete, if_true] at member
  exact gateSourceObserve_nonfixed adversary parameter auxiliary _ _ randomness rfl rfl
    selected selectedMember _ output member


/-- The source continuation preserves the chosen input, adversary state, and prefix. -/
theorem gateSourceObserve_tag {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (view : SelectedGateView)
    (output : Pipeline.Table × (AffineInput × adversary.State) × List (Sigma Garbling.oracleSpec.Answer) ×
      Garbling.Labels × Bool × List (Sigma Garbling.oracleSpec.Answer))
    (member : output ∈ (gateSourceObserve adversary parameter auxiliary table selected view data).support) :
    (output.1, output.2.1, output.2.2.1, output.2.2.2.1) =
      (table, (selected.1, selected.2.1), selected.2.2.2, sourceInputLabels data selected.1) := by
  simp only [gateSourceObserve, PMF.mem_support_map_iff] at member
  obtain ⟨result, _, rfl⟩ := member
  rfl

/-- A complete full-source continuation has the same selected input and prefix. -/
theorem fullGatePrefixKernel_tag [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (Pipeline.Table × (AffineInput × adversary.State) × List (Sigma Garbling.oracleSpec.Answer) ×
        Garbling.Labels × Bool × List (Sigma Garbling.oracleSpec.Answer)))
    (sample : Garbling.Randomness × ((RawCircuitGate → FullHashLift) × CircuitMaskTables) ×
      (AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))))
    (complete : FullSourceComplete sample.2.1.1)
    (output : Pipeline.Table × (AffineInput × adversary.State) × List (Sigma Garbling.oracleSpec.Answer) ×
      Garbling.Labels × Bool × List (Sigma Garbling.oracleSpec.Answer))
    (member : output ∈ (fullGatePrefixKernel scalar
      (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
      fallback sample).support) :
    (output.2.1, output.2.2.1) = ((sample.2.2.1, sample.2.2.2.1), sample.2.2.2.2.2) := by
  classical
  simp only [fullGatePrefixKernel, complete, if_true] at member
  have tag := gateSourceObserve_tag adversary parameter auxiliary _ _ sample.2.2 _ output member
  exact congrArg (fun value => (value.2.1, value.2.2.1)) tag

end

end Kriterion.ArgoMAC.Security
