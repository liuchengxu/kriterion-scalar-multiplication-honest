import Proof.Privacy.Source.SharedHiddenSourceTransport

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype rawBucketUseFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1

/-- The actual shared program mass fits the real source with its full public transcript. -/
theorem sharedRealSource_program_ratio [Fintype Block]
    (rest : GarblingSourceRest) (context : SharedRetained.Context)
    (linked : context.Linked rest.oracleCoin rest.algebraic.field.bridgeKey) (hidden : HiddenPublicSample)
    (mac : InputMac) (labels : context.activeCurveLabels = inputMacCoordinateEquiv mac)
    (anchor : EncPRF.PermutationIndex → Block)
    (pointGood : ¬ pointBranchCollision context.visible.2 context.rows context.input context.targets hidden.2)
    (source : FullCircuitSource) (state : Shared.Simulator.OracleState) (values : List FixedCommand)
    (queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (fixed : (sharedFixedTranscriptRecords transcript).Perm (state.fixedTranscript ++ queries))
    (fresh : FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords values))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (reference : TranscriptOracle (programRecordHistory state.fixedTranscript
      (Shared.Simulator.commandRecords values) ++ queries))
    (nonfixed : SharedNonFixedTranscriptCompatible
      (reference.1, rest.encPRFOracle, rest.hashOracle) transcript)
    (domains : SharedQueryCounts.programmedDomains (Shared.Simulator.commandRecords values) =
      sharedActiveDomains (context.gates (hidden, anchor)) (sharedCircuitSelected context.input))
    (active : ∀ gate slot,
      rawSlotBranch slot = inputSelectedLabelBit context.input (circuitGateWire gate) →
      let record := (context.gates (hidden, anchor) gate).slotRecord slot
      reference.1.permutation (Shared.fixedIndex record.index) record.domain = record.range)
    (activeFits : ∀ index, Fintype.card (SharedQueryDomain (Shared.Simulator.commandRecords values) index) ≤
      sharedCircuitBucketSize index)
    (priorFits : ∀ index,
      Fintype.card (SharedQueryDomain (Shared.Simulator.commandRecords values) index) +
        Fintype.card (SharedQueryDomain state.fixedTranscript index) ≤ Fintype.card Block)
    (residualFits : ∀ index, sharedCircuitBucketSize index +
      Fintype.card (ResidualQueryDomain (state.fixedTranscript ++ queries)
        (SharedQueryCounts.programmedDomains (Shared.Simulator.commandRecords values)) index) ≤
          Fintype.card Block) :
    (1 - ((54690772 + (364 * (state.fixedTranscript ++ queries).length : Nat)) / (2 : ENNReal) ^ 128)) *
      ((PMF.uniformOfFintype FullCircuitSource) source * Shared.Simulator.transcriptMass state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
          (fun oracle => Shared.Simulator.commands {state with fixedOracle := oracle.1} values)).toOuterMeasure
          {next | PermutationTranscriptMatches next.fixedOracle queries}) ≤
      sharedLinkedHiddenSourceMass rest (context.source hidden) (context.lifts hidden) context.input mac transcript := by
  rw [sharedLinkedHiddenSourceMass_context rest context hidden mac labels linked transcript reference.1 nonfixed]
  have recordLaw (oracle : PermutationOracle Shared.FixedKeyIndex Block) :
      PermutationTranscriptMatches oracle (sharedFixedTranscriptRecords transcript) =
        PermutationTranscriptMatches oracle (state.fixedTranscript ++ queries) := by
    apply propext
    exact ⟨fun matchRecord record member => matchRecord record (fixed.mem_iff.mpr member),
      fun matchRecord record member => matchRecord record (fixed.mem_iff.mp member)⟩
  simp_rw [recordLaw]
  exact SharedRetained.retained_program_ratio context rest.oracleCoin rest.algebraic.field.bridgeKey
    linked hidden anchor pointGood source state values queries fresh reference domains active activeFits
    priorFits residualFits

end
end Kriterion.ArgoMAC.Security
