import Proof.Privacy.Source.SharedCurveGuardAverage
import Proof.Privacy.Source.SharedProgramSourceRatio
import Proof.Privacy.Programming.SharedScheduleCompatibility

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section
set_option maxRecDepth 2048
local instance curveProgramKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveProgramKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype rawBucketUseFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1

/-- The actual curve-only program mass fits the guarded hidden-label source average. -/
theorem curveHidden_program_ratio [Fintype Block]
    (context : Context) (hidden : HiddenPublicSample) (anchor : InputMacKey)
    (pointGood : ¬ pointBranchCollision context.visible.2 context.rows context.input context.targets hidden.2)
    (source : FullCircuitSource) (state : Shared.Simulator.OracleState) (values : List FixedCommand)
    (queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords values))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (reference : TranscriptOracle (programRecordHistory state.fixedTranscript
      (Shared.Simulator.commandRecords values) ++ queries))
    (domains : SharedQueryCounts.programmedDomains (Shared.Simulator.commandRecords values) =
      sharedCurveDomains ((context.curveHidden anchor).gates (hidden, curveUnused anchor)) (sharedCircuitSelected context.input))
    (active : ∀ gate slot,
      sharedCurveSlot (Shared.fixedIndex (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) = true →
      rawSlotBranch slot = inputSelectedLabelBit context.input (circuitGateWire gate) →
      let record := ((context.curveHidden anchor).gates (hidden, curveUnused anchor) gate).slotRecord slot
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
    (1 - ((54691280 + (364 * (state.fixedTranscript ++ queries).length : Nat)) / (2 : ENNReal) ^ 128)) *
      ((PMF.uniformOfFintype FullCircuitSource) source * Shared.Simulator.transcriptMass state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
          (fun oracle => Shared.Simulator.commands {state with fixedOracle := oracle.1} values)).toOuterMeasure
          {next | PermutationTranscriptMatches next.fixedOracle queries}) ≤
      ∑' key, (PMF.uniformOfFintype InputMacKey) key *
        (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
          {fixedOracle | RawGarblingMatches ((context.curveHidden key).gates (hidden, curveUnused key)) (Shared.expandOracle fixedOracle) ∧
            PermutationTranscriptMatches fixedOracle (state.fixedTranscript ++ queries) ∧ ¬ curveHiddenPadBad context key} := by
  have compatible : PermutationTranscriptMatches reference.1 (state.fixedTranscript ++ queries) := by
    intro record member
    rcases List.mem_append.mp member with before | after
    · exact reference.2 record (List.mem_append_left queries
        ((SharedQueryCounts.mem_programRecordHistory_iff _ _ _).mpr (Or.inr before)))
    · exact reference.2 record (List.mem_append_right _ after)
  have ratio := sharedProgramSource_mass_le source state values queries fresh reference activeFits priorFits residualFits
  rw [domains] at ratio
  have average := curveHidden_guard_average_ge context hidden anchor pointGood
    reference.1 (state.fixedTranscript ++ queries) compatible active
  exact (mul_le_mul_right ratio _).trans average

end
end Kriterion.ArgoMAC.Security.SharedRetained
