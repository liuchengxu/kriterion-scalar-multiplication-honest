import Proof.Privacy.Source.SharedScheduleRatio
import Proof.Privacy.Source.SharedBucketCounts

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section
set_option maxRecDepth 2048
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype rawBucketUseFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1

/-- The actual full source and shared command interpreter fit one real factorial product. -/
theorem sharedProgramSource_mass_le [Fintype Block]
    (source : FullCircuitSource) (state : Shared.Simulator.OracleState) (values : List FixedCommand)
    (queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords values))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (reference : TranscriptOracle (programRecordHistory state.fixedTranscript
      (Shared.Simulator.commandRecords values) ++ queries))
    (activeFits : ∀ index, Fintype.card (SharedQueryDomain (Shared.Simulator.commandRecords values) index) ≤
      sharedCircuitBucketSize index)
    (priorFits : ∀ index,
      Fintype.card (SharedQueryDomain (Shared.Simulator.commandRecords values) index) +
        Fintype.card (SharedQueryDomain state.fixedTranscript index) ≤ Fintype.card Block)
    (residualFits : ∀ index, sharedCircuitBucketSize index +
      Fintype.card (ResidualQueryDomain (state.fixedTranscript ++ queries)
        (SharedQueryCounts.programmedDomains (Shared.Simulator.commandRecords values)) index) ≤
          Fintype.card Block) :
    (PMF.uniformOfFintype FullCircuitSource) source * Shared.Simulator.transcriptMass state.fixedTranscript *
      ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
        (fun oracle => Shared.Simulator.commands {state with fixedOracle := oracle.1} values)).toOuterMeasure
        {next | PermutationTranscriptMatches next.fixedOracle queries} ≤
      ∏ index : Shared.FixedKeyIndex,
        ((Fintype.card Block - (sharedCircuitBucketSize index +
          Fintype.card (ResidualQueryDomain (state.fixedTranscript ++ queries)
            (SharedQueryCounts.programmedDomains (Shared.Simulator.commandRecords values)) index))).factorial : ENNReal) /
              (Fintype.card Block).factorial := by
  have before : PermutationTranscriptMatches reference.1 state.fixedTranscript := by
    intro record member
    exact reference.2 record (List.mem_append_left queries
      ((SharedQueryCounts.mem_programRecordHistory_iff _ _ _).mpr (Or.inr member)))
  rw [sharedFullCircuitSource_uniform_mass,
    sharedTranscriptMass_eq_product reference.1 _ before,
    Shared.Simulator.commands_queryMass_product state values queries fresh reference]
  let active := fun index => Fintype.card (SharedQueryDomain (Shared.Simulator.commandRecords values) index)
  let hidden := fun index => sharedCircuitBucketSize index - active index
  let prior := fun index => Fintype.card (SharedQueryDomain state.fixedTranscript index)
  let residual := fun index => Fintype.card (ResidualQueryDomain (state.fixedTranscript ++ queries)
    (SharedQueryCounts.programmedDomains (Shared.Simulator.commandRecords values)) index)
  have count (index : Shared.FixedKeyIndex) : active index + hidden index = sharedCircuitBucketSize index :=
    Nat.add_sub_of_le (activeFits index)
  have bound := sharedSourceTranscriptFactor_le (Fintype.card Block) active hidden prior residual
    Fintype.card_pos priorFits (fun index => by simpa only [count] using residualFits index)
  simpa only [count] using bound

end
end Kriterion.ArgoMAC.Security
