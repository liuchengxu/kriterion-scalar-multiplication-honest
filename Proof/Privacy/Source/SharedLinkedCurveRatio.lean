import Proof.Privacy.Source.SharedCurveIndependentRatio
import Proof.Privacy.Source.SharedIndependentSourceMass
import Proof.Privacy.Source.SharedEncGuardedAverage

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section
set_option maxRecDepth 2048
attribute [local irreducible] pipelineGateSchedule scheduleCommands Shared.Simulator.commandRecords
  circuitMaskSampleGarble sourceGatePrescription PMF.uniformOfFintype
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1 instFintypeEncQueryDomainOfBlock
  instDecidableEqRawCircuitGate_1
local instance linkedCurveGateDecidableEq : DecidableEq RawCircuitGate := fun a b => FinEnum.decEq a b
local instance linkedCurveKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance linkedCurveKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The actual curve-only program fits the actual linked source after its EncPRF average. -/
theorem sharedCurveSource_linked_ratio [Fintype Block]
    (rest : GarblingSourceRest) (context : SharedRetained.Context)
    (hidden : HiddenPublicSample) (anchor : InputMacKey)
    (rows : FieldMacToECMac.Rows) (state : Shared.Simulator.OracleState)
    (queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (fixed : (sharedFixedTranscriptRecords transcript).Perm (state.fixedTranscript ++ queries))
    (miss : rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (sharedLegacyTranscript transcript))
    (pointGood : ¬ pointBranchCollision context.visible.2 context.rows context.input context.targets hidden.2)
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : transcript.length ≤ budget)
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    let source := context.source hidden
    let curveKey := context.curveKey (SharedRetained.curveUnused anchor)
    let mac := curveKey.encodeAffine context.input
    let sample := circuitMaskSampleGarble rest.algebraic.field.bridgeKey context.mask rows context.input source
    let values := scheduleCommands (sample.curveRequest.schedule context.input mac)
    FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords values) →
    ((1 - ((4 * budget : Nat) : ENNReal) / Fintype.card Block) *
      encTranscriptFactor (encOracleTranscriptRecords (sharedLegacyTranscript transcript))) *
      (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
        if SharedNonFixedTranscriptCompatible (state.fixedOracle, rest.encPRFOracle, hash) transcript then
          (1 - ((54691280 + (364 * (state.fixedTranscript ++ queries).length : Nat)) / (2 : ENNReal) ^ 128)) *
            ((PMF.uniformOfFintype FullCircuitSource) (context.lifts hidden, sourceCiphertexts source) *
              Shared.Simulator.transcriptMass state.fixedTranscript *
              ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
                (fun oracle => Shared.Simulator.commands {state with fixedOracle := oracle.1} values)).toOuterMeasure
                {next | PermutationTranscriptMatches next.fixedOracle queries}) else 0) ≤
      ∑' enc : PermutationOracle EncPRF.PermutationIndex Block,
        (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) enc *
          ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
            sharedLinkedHiddenSourceMass {rest with encPRFOracle := enc, hashOracle := hash}
              source (context.lifts hidden) context.input mac transcript := by
  dsimp only
  intro fresh
  let source := context.source hidden
  let curveKey := context.curveKey (SharedRetained.curveUnused anchor)
  let mac := curveKey.encodeAffine context.input
  have fixedBudget : (state.fixedTranscript ++ queries).length ≤ 2 ^ 101 := by
    rw [← fixed.length_eq]
    exact (sharedFixedTranscriptRecords_length transcript).trans (lengthBound.trans small)
  have fits (index : EncPRF.PermutationIndex) : 2 + Fintype.card
      (EncQueryDomain (encOracleTranscriptRecords (sharedLegacyTranscript transcript)) index) ≤ Fintype.card Block := by
    classical
    have count : Fintype.card (EncQueryDomain (encOracleTranscriptRecords (sharedLegacyTranscript transcript)) index) ≤
        (sharedLegacyTranscript transcript).length :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)).trans
        (encExternalQueryCount_le (sharedLegacyTranscript transcript))
    rw [sharedLegacyTranscript_length] at count
    have card : Fintype.card Block = 2 ^ 128 :=
      (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
    rw [card]
    omega
  have link := sharedEnc_guarded_average_ge rest source (context.lifts hidden) context.input mac
    transcript miss budget lengthBound fits
  change _ * (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
    sharedIndependentHiddenSourceMass {rest with hashOracle := hash} source (context.lifts hidden)
      context.input mac transcript) ≤ _ at link
  apply le_trans _ link
  apply mul_le_mul_right
  apply ENNReal.tsum_le_tsum
  intro hash
  apply mul_le_mul_right
  by_cases nonfixed : SharedNonFixedTranscriptCompatible (state.fixedOracle, rest.encPRFOracle, hash) transcript
  · rw [if_pos nonfixed]
    rw [sharedIndependentHiddenSourceMass_fixed {rest with hashOracle := hash}
      source (context.lifts hidden) context.input mac transcript state.fixedOracle nonfixed]
    have matching (oracle : PermutationOracle Shared.FixedKeyIndex Block) :
        PermutationTranscriptMatches oracle (sharedFixedTranscriptRecords transcript) ↔
          PermutationTranscriptMatches oracle (state.fixedTranscript ++ queries) := by
      simp only [PermutationTranscriptMatches, fixed.mem_iff]
    simp_rw [matching]
    have labels : context.activeCurveLabels = inputMacCoordinateEquiv mac := by
      have selected := congrArg Prod.fst
        ((selectedKeyLabelsEquiv (inputSelectedLabelBit context.input)).apply_symm_apply
          (context.activeCurveLabels, SharedRetained.curveUnused anchor))
      exact selected.symm.trans ((selectedKeyLabels_public_iff context.input curveKey mac).mpr rfl)
    have keys (unused : EncPRF.PermutationIndex → Block) : context.curveKey unused =
        (selectedKeyLabelsEquiv (inputSelectedLabelBit context.input)).symm (inputMacCoordinateEquiv mac, unused) := by
      unfold SharedRetained.Context.curveKey
      rw [labels]
    have ratio := sharedCurveSource_independent_ratio rest.algebraic.field.bridgeKey context hidden anchor rows state queries
      pointGood fixedBudget
    dsimp only at ratio
    have bound := ratio fresh
    have keyFunctions : context.curveKey = fun unused =>
        (selectedKeyLabelsEquiv (inputSelectedLabelBit context.input)).symm
          (inputMacCoordinateEquiv mac, unused) := funext keys
    conv_rhs at bound => rw [keyFunctions]
    exact bound
  · rw [if_neg nonfixed]
    exact bot_le

end
end Kriterion.ArgoMAC.Security
