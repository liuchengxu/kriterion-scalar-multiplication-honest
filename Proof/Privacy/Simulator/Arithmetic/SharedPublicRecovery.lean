import Proof.Privacy.Simulator.Arithmetic.SharedSourceCutoff
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicOperational

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle
open Security.SharedSimulatorMachine
noncomputable section

/-- The inverse reply determines its complete next programmed table. -/
theorem programmedInverse_recover (attempts : Nat) (state : ProgrammedPermutation (2 ^ 128))
    (input : Fin (2 ^ 128)) :
    (drawCutoffLaw attempts (state.inverse input)).map
      (Option.map fun result => (result.1, programmedInverseNext state input result.1)) =
      drawCutoffLaw attempts (state.inverse input) := by
  have recovered := sparseForward_recover attempts state.base.reverse ((swaps state.overlay).symm input)
  have mapped := congrArg (PMF.map (Option.map fun result : Fin (2 ^ 128) × SparsePermutation (2 ^ 128) =>
    (result.1, (⟨result.2.reverse, state.overlay⟩ : ProgrammedPermutation (2 ^ 128))))) recovered
  simpa only [ProgrammedPermutation.inverse, SparsePermutation.inverse_reverse_forward,
    drawCutoffLaw_map, PMF.map_comp, Function.comp_def, Option.map_map, programmedInverseNext] using mapped

/-- The hash reply determines its complete next finite table. -/
theorem hashSource_recover (pairs : HashTable BN254.BaseField (2 ^ 256)) (key : BN254.BaseField) :
    (pairs.query (by decide) key).distribution.map (fun result => (result.1, hashNextTable pairs key result.1)) =
      (pairs.query (by decide) key).distribution := by
  cases known : pairs.lookup key <;>
    simp [HashTable.query, known, Draw.distribution, hashNextTable, PMF.pure_map, PMF.map_comp, Function.comp_def]

/-- Each public reply determines the next physical family. -/
def sharedPublicNextFamily (state : SparseOracleFamily) :
    (request : SharedQuery) → SharedAnswer request → SparseOracleFamily
  | .fixedForward index value, reply =>
      let oracle := sharedPhysicalIndex (.inl index)
      state.updatePermutation oracle (programmedForwardNext (state.permutations oracle) (blockFin value) (blockFin reply))
  | .fixedInverse index value, reply =>
      let oracle := sharedPhysicalIndex (.inl index)
      state.updatePermutation oracle (programmedInverseNext (state.permutations oracle) (blockFin value) (blockFin reply))
  | .encForward index value, reply =>
      let oracle := sharedPhysicalIndex (.inr index)
      state.updatePermutation oracle (programmedForwardNext (state.permutations oracle) (blockFin value) (blockFin reply))
  | .encInverse index value, reply =>
      let oracle := sharedPhysicalIndex (.inr index)
      state.updatePermutation oracle (programmedInverseNext (state.permutations oracle) (blockFin value) (blockFin reply))
  | .hash key, reply => state.updateHash (hashNextTable state.hash key (hashFin reply))

/-- Each public reply determines the next family and its visible transcript entry. -/
def sharedPublicNext (state : SharedOracleSource) (request : SharedQuery)
    (reply : SharedAnswer request) : SharedOracleSource :=
  ⟨sharedPublicNextFamily state.family request reply, state.metadata.record request reply⟩

/-- Reply recovery preserves the complete shared public source law. -/
theorem sharedPublic_recover (attempts : Nat) (state : SharedOracleSource) (request : SharedQuery) :
    (sharedSourceCutoff attempts (.inr request) state).map
      (Option.map fun result => (result.1, sharedPublicNext state request result.1)) =
      sharedSourceCutoff attempts (.inr request) state := by
  cases request with
  | fixedForward index value =>
      have law := programmedForward_recover attempts
        (state.family.permutations (sharedPhysicalIndex (.inl index))) (blockFin value)
      have mapped := congrArg (PMF.map (Option.map fun result =>
        (blockFin.symm result.1, (⟨state.family.updatePermutation (sharedPhysicalIndex (.inl index)) result.2,
          state.metadata.record (.fixedForward index value) (blockFin.symm result.1)⟩ : SharedOracleSource)))) law
      simp only [sharedSourceCutoff, sharedSourceExactQuery, Bool.false_eq_true, if_false,
        sharedCombinedSourceDraw, sharedExternalSourceDraw, sharedInternalSourceDraw, lowerRequest,
        physicalRequest, oracleFamilyDraw, familyDraw, lowerAnswer, namedAnswer,
        drawCutoffLaw_map, PMF.map_comp, Option.map_map, Function.comp_def,
        sharedPublicNext, sharedPublicNextFamily, Equiv.apply_symm_apply, SparseOracleFamily.updatePermutation] at mapped ⊢
      convert mapped using 1 <;> congr 1 <;> funext result <;> cases result <;> rfl
  | encForward index value =>
      have law := programmedForward_recover attempts
        (state.family.permutations (sharedPhysicalIndex (.inr index))) (blockFin value)
      have mapped := congrArg (PMF.map (Option.map fun result =>
        (blockFin.symm result.1, (⟨state.family.updatePermutation (sharedPhysicalIndex (.inr index)) result.2,
          state.metadata.record (.encForward index value) (blockFin.symm result.1)⟩ : SharedOracleSource)))) law
      simp only [sharedSourceCutoff, sharedSourceExactQuery, Bool.false_eq_true, if_false,
        sharedCombinedSourceDraw, sharedExternalSourceDraw, sharedInternalSourceDraw, lowerRequest,
        physicalRequest, oracleFamilyDraw, familyDraw, lowerAnswer, namedAnswer,
        drawCutoffLaw_map, PMF.map_comp, Option.map_map, Function.comp_def,
        sharedPublicNext, sharedPublicNextFamily, Equiv.apply_symm_apply, SparseOracleFamily.updatePermutation] at mapped ⊢
      convert mapped using 1 <;> congr 1 <;> funext result <;> cases result <;> rfl
  | fixedInverse index value =>
      have law := programmedInverse_recover attempts
        (state.family.permutations (sharedPhysicalIndex (.inl index))) (blockFin value)
      have mapped := congrArg (PMF.map (Option.map fun result =>
        (blockFin.symm result.1, (⟨state.family.updatePermutation (sharedPhysicalIndex (.inl index)) result.2,
          state.metadata.record (.fixedInverse index value) (blockFin.symm result.1)⟩ : SharedOracleSource)))) law
      simp only [sharedSourceCutoff, sharedSourceExactQuery, Bool.false_eq_true, if_false,
        sharedCombinedSourceDraw, sharedExternalSourceDraw, sharedInternalSourceDraw, lowerRequest,
        physicalRequest, oracleFamilyDraw, familyDraw, lowerAnswer, namedAnswer,
        drawCutoffLaw_map, PMF.map_comp, Option.map_map, Function.comp_def,
        sharedPublicNext, sharedPublicNextFamily, Equiv.apply_symm_apply, SparseOracleFamily.updatePermutation] at mapped ⊢
      convert mapped using 1 <;> congr 1 <;> funext result <;> cases result <;> rfl
  | encInverse index value =>
      have law := programmedInverse_recover attempts
        (state.family.permutations (sharedPhysicalIndex (.inr index))) (blockFin value)
      have mapped := congrArg (PMF.map (Option.map fun result =>
        (blockFin.symm result.1, (⟨state.family.updatePermutation (sharedPhysicalIndex (.inr index)) result.2,
          state.metadata.record (.encInverse index value) (blockFin.symm result.1)⟩ : SharedOracleSource)))) law
      simp only [sharedSourceCutoff, sharedSourceExactQuery, Bool.false_eq_true, if_false,
        sharedCombinedSourceDraw, sharedExternalSourceDraw, sharedInternalSourceDraw, lowerRequest,
        physicalRequest, oracleFamilyDraw, familyDraw, lowerAnswer, namedAnswer,
        drawCutoffLaw_map, PMF.map_comp, Option.map_map, Function.comp_def,
        sharedPublicNext, sharedPublicNextFamily, Equiv.apply_symm_apply, SparseOracleFamily.updatePermutation] at mapped ⊢
      convert mapped using 1 <;> congr 1 <;> funext result <;> cases result <;> rfl
  | hash key =>
      have law := hashSource_recover state.family.hash key
      have mapped := congrArg (PMF.map fun result => some
        (hashFin.symm result.1,
          (⟨state.family.updateHash result.2, state.metadata.record (.hash key)
            (hashFin.symm result.1)⟩ : SharedOracleSource))) law
      simp only [sharedSourceCutoff, sharedSourceExactQuery, if_true, sharedCombinedSourceHandler,
        sharedCombinedSourceDraw, sharedExternalSourceDraw, sharedInternalSourceDraw, lowerRequest,
        physicalRequest, oracleFamilyDraw, lowerAnswer, namedAnswer, Draw.map_distribution,
        PMF.map_comp, Function.comp_def, Option.map_some, sharedPublicNext, sharedPublicNextFamily,
        Equiv.apply_symm_apply] at mapped ⊢
      exact mapped

end
end Kriterion.ArgoMAC.ArithmeticSimulator
