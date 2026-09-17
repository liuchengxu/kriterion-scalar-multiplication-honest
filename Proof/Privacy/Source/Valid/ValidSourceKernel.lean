import Proof.Privacy.Source.ActualSourceRatio
import Proof.Privacy.Transcript.IdealGateGame

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] fixedQueryDomainFintype transcriptOracleFintype

local instance : Fintype InputMacKey := publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- This key represents one selected public label vector. -/
def selectedPublicKey (input : AffineInput) (labels : EncPRF.PermutationIndex → Block) : InputMacKey :=
  (selectedKeyLabelsEquiv (inputSelectedLabelBit input)).symm (labels, fun _ => 0)

/-- The representative key gives exactly the selected public input MAC. -/
theorem selectedPublicKey_encode (input : AffineInput) (labels : EncPRF.PermutationIndex → Block) :
    (selectedPublicKey input labels).encodeAffine input = inputMacCoordinateEquiv.symm labels := by
  apply inputMacCoordinateEquiv.injective
  rw [Equiv.apply_symm_apply, ← selectedKeyLabels_inputMac]
  change ((selectedKeyLabelsEquiv (inputSelectedLabelBit input))
    ((selectedKeyLabelsEquiv (inputSelectedLabelBit input)).symm (labels, fun _ => 0))).1 = labels
  rw [Equiv.apply_symm_apply]

/-- A uniform input key gives exact uniform selected coordinate labels. -/
theorem map_uniform_selectedLabels [Fintype Block] (input : AffineInput) :
    (PMF.uniformOfFintype InputMacKey).map
      (fun key => inputMacCoordinateEquiv (key.encodeAffine input)) =
      PMF.uniformOfFintype (EncPRF.PermutationIndex → Block) := by
  have law := congrArg (fun distribution => distribution.map Prod.fst)
    (map_uniform_selectedKeyLabels (inputSelectedLabelBit input))
  simpa only [PMF.map_comp, Function.comp_def, selectedKeyLabels_inputMac,
    map_uniform_prod_fst] using law

/-- The first adversary phase does not receive the unused input-key labels. -/
theorem gateSourceChoose_rekey {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (table : Pipeline.Table)
    (data : GarblingOracleData) (key : InputMacKey) :
    gateSourceChoose adversary parameter auxiliary table {data with inputMacKey := key} =
      gateSourceChoose adversary parameter auxiliary table data := rfl

/-- The second adversary phase receives only the selected public input MAC. -/
theorem gateSourceObserve_rekey {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (table : Pipeline.Table)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (view : SelectedGateView) (data : GarblingOracleData) (key : InputMacKey)
    (same : key.encodeAffine selected.1 = data.inputMacKey.encodeAffine selected.1) :
    gateSourceObserve adversary parameter auxiliary table selected view {data with inputMacKey := key} =
      gateSourceObserve adversary parameter auxiliary table selected view data := by
  simp only [gateSourceObserve, sourceInputLabels, same]

set_option maxRecDepth 4096 in
/-- The actual source kernel samples selected public labels after the input choice. -/
theorem gateSourceKernel_selectedLabels [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (table : Pipeline.Table)
    (view : AffineInput → SelectedGateView) (data : GarblingOracleData) :
    (PMF.uniformOfFintype InputMacKey).bind (fun key =>
      (gateSourceChoose adversary parameter auxiliary table {data with inputMacKey := key}).bind fun selected =>
        gateSourceObserve adversary parameter auxiliary table selected (view selected.1)
          {data with inputMacKey := key}) =
    (gateSourceChoose adversary parameter auxiliary table data).bind fun selected =>
      (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).bind fun labels =>
        gateSourceObserve adversary parameter auxiliary table selected (view selected.1)
          {data with inputMacKey := selectedPublicKey selected.1 labels} := by
  simp_rw [gateSourceChoose_rekey]
  rw [PMF.bind_comm]
  apply congrArg (fun kernel => (gateSourceChoose adversary parameter auxiliary table data).bind kernel)
  funext selected
  rw [← map_uniform_selectedLabels selected.1, PMF.bind_map]
  apply congrArg (fun kernel => (PMF.uniformOfFintype InputMacKey).bind kernel)
  funext key
  apply (gateSourceObserve_rekey adversary parameter auxiliary table selected (view selected.1)
    {data with inputMacKey := key} _ ?_).symm
  rw [selectedPublicKey_encode, Equiv.symm_apply_apply]


/-- Equal fixed-oracle replies give the same recorded state fields. -/
theorem idealHandler_updateFixed (state : SimulatorState)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) (query : Garbling.oracleSpec.Query)
    (same : (idealOracleHandler query {state with fixedOracle := oracle}).1 =
      (idealOracleHandler query state).1) :
    (idealOracleHandler query {state with fixedOracle := oracle}).2 =
      {(idealOracleHandler query state).2 with fixedOracle := oracle} := by
  cases query <;>
    simp only [idealOracleHandler, oracleHandlerFor, recordFixed, recordEnc, recordHash] at same ⊢
  all_goals try rw [same]

/-- A compatible prefix keeps all recorded fields when its fixed oracle changes. -/
theorem idealTranscriptFinal_updateFixed (state : SimulatorState)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (history : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler state history)
    (updated : OracleTranscriptCompatible idealOracleHandler {state with fixedOracle := oracle} history) :
    transcriptFinalState idealOracleHandler {state with fixedOracle := oracle} history =
      {transcriptFinalState idealOracleHandler state history with fixedOracle := oracle} := by
  induction history generalizing state with
  | nil => rfl
  | cons entry tail inductionHypothesis =>
      rcases entry with ⟨query, answer⟩
      change _ ∧ _ at compatible updated
      have next := idealHandler_updateFixed state oracle query (updated.1.trans compatible.1.symm)
      simp only [transcriptFinalState]
      rw [next]
      apply inductionHypothesis _ compatible.2
      rw [← next]
      exact updated.2


/-- A compatible retained prefix fixes exactly its recorded permutation equations. -/
theorem idealPrefixCompatible_iff_matches (state : SimulatorState) (randomness : Garbling.Randomness)
    (before : List (Sigma Garbling.oracleSpec.Answer))
    (enc : state.encOracle = randomness.encPRFOracle) (hash : state.hashOracle = randomness.hashOracle)
    (compatible : OracleTranscriptCompatible idealOracleHandler state before)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) :
    OracleTranscriptCompatible idealOracleHandler {state with fixedOracle := oracle} before ↔
      PermutationTranscriptMatches oracle (fixedOracleTranscriptRecords before) := by
  have retained := (idealOracleTranscriptCompatible_iff_real state
    {randomness with fixedKeyOracle := state.fixedOracle} before rfl enc hash).mp compatible
  rw [realOracleTranscriptCompatible_iff, nonFixedTranscriptCompatible_update] at retained
  rw [idealOracleTranscriptCompatible_iff_real {state with fixedOracle := oracle} {randomness with fixedKeyOracle := oracle}
    before rfl enc hash, realOracleTranscriptCompatible_iff, nonFixedTranscriptCompatible_update]
  exact and_iff_left retained.2

/-- A fixed transcript gives a conditional uniform oracle law. -/
theorem fixedTranscript_event_mass [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (reference : PermutationOracle Pipeline.FixedKeyIndex Block)
    (matchingHistory : PermutationTranscriptMatches reference history)
    (event : PermutationOracle Pipeline.FixedKeyIndex Block → Prop)
    [Nonempty (TranscriptOracle history)] :
    (PMF.uniformOfFintype (PermutationOracle Pipeline.FixedKeyIndex Block)).toOuterMeasure
      {oracle | PermutationTranscriptMatches oracle history ∧ event oracle} =
    fixedTranscriptFactor history *
      (PMF.uniformOfFintype (TranscriptOracle history)).toOuterMeasure {oracle | event oracle.1} := by
  have mass := @uniformSubtype_mass_mul (PermutationOracle Pipeline.FixedKeyIndex Block)
    inferInstance inferInstance (PermutationTranscriptMatches · history) event
    (transcriptOracleFintype history) ⟨⟨reference, matchingHistory⟩⟩
  rw [fixedTranscriptFactor_eq_mass reference history matchingHistory] at mass
  exact mass.symm

set_option maxRecDepth 4096 in
/-- The prefix source mass gives the exact conditional programmed-oracle experiment. -/
theorem idealPrefixProgrammed_mass [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (state : SimulatorState) (randomness : Garbling.Randomness)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (schedule : List GateDirective)
    (empty : state.fixedTranscript = [])
    (enc : state.encOracle = randomness.encPRFOracle) (hash : state.hashOracle = randomness.hashOracle)
    (compatible : OracleTranscriptCompatible idealOracleHandler state before)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler state before).fixedTranscript)] :
    (PMF.uniformOfFintype (PermutationOracle Pipeline.FixedKeyIndex Block)).toOuterMeasure
      {oracle | OracleTranscriptCompatible idealOracleHandler {state with fixedOracle := oracle} before ∧
        OracleTranscriptCompatible idealOracleHandler
          (programGateSchedule (transcriptFinalState idealOracleHandler {state with fixedOracle := oracle} before)
            schedule) after} =
    fixedTranscriptFactor (transcriptFinalState idealOracleHandler state before).fixedTranscript *
      ((PMF.uniformOfFintype
        (TranscriptOracle (transcriptFinalState idealOracleHandler state before).fixedTranscript)).map
          (fun oracle => programGateSchedule
            {transcriptFinalState idealOracleHandler state before with fixedOracle := oracle.1} schedule)).toOuterMeasure
              {programmed | OracleTranscriptCompatible idealOracleHandler programmed after} := by
  have history := idealTranscriptFinal_fixedHistory state before compatible
  rw [empty, List.append_nil] at history
  have matchingHistory (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) :
      PermutationTranscriptMatches oracle
        (transcriptFinalState idealOracleHandler state before).fixedTranscript ↔
      PermutationTranscriptMatches oracle (fixedOracleTranscriptRecords before) := by
    rw [history]
    simp only [PermutationTranscriptMatches, List.mem_reverse]
  have original : PermutationTranscriptMatches state.fixedOracle
      (transcriptFinalState idealOracleHandler state before).fixedTranscript := by
    apply (matchingHistory _).mpr
    exact (idealPrefixCompatible_iff_matches state randomness before enc hash compatible state.fixedOracle).mp compatible
  rw [PMF.toOuterMeasure_map_apply]
  simp only [Set.preimage_setOf_eq]
  rw [← fixedTranscript_event_mass _ state.fixedOracle original
    (fun oracle => OracleTranscriptCompatible idealOracleHandler
      (programGateSchedule {transcriptFinalState idealOracleHandler state before with fixedOracle := oracle} schedule) after)]
  apply congrArg (PMF.toOuterMeasure (PMF.uniformOfFintype (PermutationOracle Pipeline.FixedKeyIndex Block)))
  ext oracle
  simp only [Set.mem_setOf_eq]
  have prefixLaw := idealPrefixCompatible_iff_matches state randomness before enc hash compatible oracle
  rw [matchingHistory, ← prefixLaw]
  apply and_congr_right
  intro valid
  rw [idealTranscriptFinal_updateFixed state oracle before compatible valid]

end
end Kriterion.ArgoMAC.Security
