import Proof.Privacy.Simulator.Arithmetic.EncLinkReindex
import Proof.Privacy.Simulator.Arithmetic.ProgramCutoffReindex
import Proof.Privacy.Simulator.Arithmetic.SharedSourceProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Security Security.SimulatorMachine Security.SharedSimulatorMachine
noncomputable section

/-- The shared link uses the same read requests without recording public history. -/
def encLinkSharedRequest : encLinkReadSpec.Query → SharedSimulatorMachine.combinedSpec.Query
  | .inl (index, input) => .inl (.read (.encForward index input))
  | .inr key => .inl (.read (.hash key))

/-- The shared link reply already has the common typed representation. -/
def encLinkSharedAnswer : (query : encLinkReadSpec.Query) →
    SharedSimulatorMachine.combinedSpec.Answer (encLinkSharedRequest query) → encLinkReadSpec.Answer query
  | .inl _, value => value
  | .inr _, value => value

/-- The common link syntax has the exact shared compiler image. -/
theorem encLinkReadProgram_shared {A : Type} {budget : Nat} (program : Program encLinkReadSpec A budget) :
    program.reindex encLinkSharedRequest encLinkSharedAnswer =
      sharedCombinedProgram (program.reindex encLinkOriginalRequest encLinkOriginalAnswer) := by
  induction program with
  | pure => rfl
  | query query next ih =>
      simp only [sharedCombinedProgram] at ih
      cases query <;> simp only [Program.reindex, encLinkSharedRequest, encLinkSharedAnswer,
        encLinkOriginalRequest, encLinkOriginalAnswer, sharedCombinedProgram, sharedInternalRequest,
        sharedInternalAnswer]
      all_goals
        congr 1
        funext value
        exact ih value
  | map f program ih => simpa only [Program.reindex, sharedCombinedProgram] using congrArg (Program.map f) ih
  | bind program next first second => simp only [Program.reindex, sharedCombinedProgram, first, second]
  | weaken program bound ih => simpa only [Program.reindex, sharedCombinedProgram] using congrArg (fun p => Program.weaken p bound) ih

/-- The common EncPRF index has the exact shared physical address. -/
theorem encLinkPhysicalIndex_shared (index : EncPRF.PermutationIndex) :
    sharedPhysicalIndex (.inr index) = encLinkPhysicalIndex index := by
  apply Fin.ext
  rw [sharedPhysicalIndex_enc]
  exact Nat.add_comm _ _

/-- Each link read preserves its reply and the unchanged shared transcript metadata. -/
theorem encLinkRead_cutoff (attempts : Nat) (query : encLinkReadSpec.Query)
    (state : SparseOracleFamily) (metadata : SharedSimulatorMachine.Metadata) :
    ((oracleFamilyCutoff attempts (encLinkPhysicalRequest query) state).map
      (Option.map fun result => (encLinkPhysicalAnswer query result.1, result.2))).map
        (Option.map fun result => (result.1, (⟨result.2, metadata⟩ : SharedOracleSource))) =
      (sharedSourceCutoff attempts (encLinkSharedRequest query) ⟨state, metadata⟩).map
        (Option.map fun result => (encLinkSharedAnswer query result.1, result.2)) := by
  cases query with
  | inl pair =>
      obtain ⟨index, input⟩ := pair
      simp only [encLinkSharedRequest, encLinkSharedAnswer, encLinkPhysicalRequest, encLinkPhysicalAnswer,
        sharedSourceCutoff, sharedSourceExactQuery, Bool.false_eq_true, ↓reduceIte,
        sharedCombinedSourceDraw, sharedInternalSourceDraw, SharedSimulatorMachine.lowerRequest, physicalRequest,
        encLinkPhysicalIndex_shared, SharedSimulatorMachine.lowerAnswer, namedAnswer, drawCutoffLaw_map, oracleFamilyCutoff,
        PMF.map_comp, Function.comp_def, Option.map_map]
      have blocks : SharedSimulatorMachine.blockFin = SimulatorMachine.blockFin := rfl
      rw [encLinkPhysicalIndex_shared index, blocks]
  | inr key =>
      simp only [encLinkSharedRequest, encLinkSharedAnswer, encLinkPhysicalRequest, encLinkPhysicalAnswer,
        sharedSourceCutoff, sharedSourceExactQuery, ↓reduceIte, sharedCombinedSourceHandler,
        sharedCombinedSourceDraw, sharedInternalSourceDraw, SharedSimulatorMachine.lowerRequest, physicalRequest,
        SharedSimulatorMachine.lowerAnswer, namedAnswer, OperationalOracle.Draw.map_distribution, oracleFamilyCutoff,
        oracleFamilySampled, PMF.map_comp, Function.comp_def, Option.map_map]
      rfl

/-- The physical link source has the exact internal shared cutoff law. -/
theorem encLinkProgram_sharedCutoff (attempts : Nat) (curve : CurveGateRequest) (input : AffineInput)
    (mac : InputMac) (state : SparseOracleFamily) (metadata : SharedSimulatorMachine.Metadata) :
    (runSampledCutoff (oracleFamilyCutoff attempts) (encLinkProgram curve input mac).toOracle state).map
      (Option.map fun result => (result.1, (⟨result.2, metadata⟩ : SharedOracleSource))) =
      runSampledCutoff (sharedSourceCutoff attempts)
        (sharedCombinedProgram (link curve input mac)).toOracle ⟨state, metadata⟩ := by
  rw [← encLinkReadProgram_physical, ← encLinkReadProgram_original, ← encLinkReadProgram_shared]
  simp only [Program.cutoffLaw_toOracle, Program.reindex_cutoffLaw]
  exact Program.cutoffLaw_decode (encLinkReadProgram curve input mac) _ _
    (fun family => (⟨family, metadata⟩ : SharedOracleSource))
    (fun query current => encLinkRead_cutoff attempts query current metadata) state

end
end Kriterion.ArgoMAC.ArithmeticSimulator
