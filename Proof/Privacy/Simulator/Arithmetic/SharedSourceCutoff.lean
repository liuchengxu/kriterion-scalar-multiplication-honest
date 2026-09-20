import Proof.Privacy.Simulator.Arithmetic.SharedFamilySource
import Proof.Privacy.Simulator.Arithmetic.OracleFamilyInitial

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security.OperationalOracle Security.SharedSimulatorMachine Security.SimulatorSampling
open scoped ENNReal
noncomputable section

/-- Hash requests use the exact two-block sampler on both internal and external paths. -/
def sharedSourceExactQuery : combinedSpec.Query → Bool
  | .inl (.read (.hash _)) => true
  | .inr (.hash _) => true
  | _ => false

/-- The shared source retains every finite cutoff failure and every exact hash result. -/
def sharedSourceCutoff (attempts : Nat) (query : combinedSpec.Query) (state : SharedOracleSource) :
    PMF (Option (combinedSpec.Answer query × SharedOracleSource)) :=
  if sharedSourceExactQuery query then (sharedCombinedSourceHandler query state).map some
  else drawCutoffLaw attempts (sharedCombinedSourceDraw query state)

/-- Each shared source operation retains the checked lower fraction of its exact joint mass. -/
theorem sharedSourceCutoff_lower (attempts : Nat) (query : combinedSpec.Query) (state : SharedOracleSource)
    (result : combinedSpec.Answer query × SharedOracleSource) :
    retained attempts * sharedCombinedSourceHandler query state result ≤
      sharedSourceCutoff attempts query state (some result) := by
  unfold sharedSourceCutoff
  split
  · rw [mapSome_apply]
    exact mul_le_of_le_one_left' tsub_le_self
  · exact drawCutoffLaw_lower attempts (sharedCombinedSourceDraw query state) result

/-- A complete shared source run has at most one cutoff loss per declared operation. -/
theorem sharedSourceCutoff_failure (attempts : Nat) {Result : Type} {budget : Nat}
    (program : OracleProgram combinedSpec Result budget) (state : SharedOracleSource) :
    runSampledCutoff (sharedSourceCutoff attempts) program state none ≤ budget * (2 : ENNReal)⁻¹ ^ attempts :=
  (runSampledCutoff_failure sharedCombinedSourceHandler (sharedSourceCutoff attempts) (retained attempts) tsub_le_self
    (sharedSourceCutoff_lower attempts) program state).trans
      (loss_pow_le _ (pow_le_one₀ zero_le (by norm_num)) budget)

/-- The cutoff bound covers every adaptive interleaving of public queries and checked programming. -/
theorem sharedSourceCutoff_event (attempts : Nat) {Result : Type} {budget : Nat}
    (program : OracleProgram combinedSpec Result budget) (state : SharedOracleSource)
    (event : Set (Option (Result × SharedOracleSource))) :
    |((runSampledCutoff (sharedSourceCutoff attempts) program state).toOuterMeasure event).toReal -
      (((runSampled sharedCombinedSourceHandler program state).map some).toOuterMeasure event).toReal| ≤
      budget * (2 : ℝ)⁻¹ ^ attempts := by
  apply (runSampledCutoff_event_bound sharedCombinedSourceHandler (sharedSourceCutoff attempts)
    (retained attempts) tsub_le_self (sharedSourceCutoff_lower attempts) program state event).trans
  have loss := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top budget) (by finiteness))
    (loss_pow_le ((2 : ENNReal)⁻¹ ^ attempts) (pow_le_one₀ zero_le (by norm_num)) budget)
  simpa only [retained, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat] using loss

/-- The empty physical source begins with the supplied transcript metadata. -/
def initialSharedOracleSource (metadata : Metadata) : SharedOracleSource := ⟨emptyOracleFamily, metadata⟩

/-- The empty physical completion has the actual uniform shared oracle law. -/
theorem initialSharedOracleSource_completion (metadata : Metadata) :
    let : Nonempty SharedOracleCoin := ⟨defaultSharedOracleCoin⟩
    sharedSourceCompletion (initialSharedOracleSource metadata) =
      (PMF.uniformOfFintype SharedOracleCoin).map (withOracles metadata) := by
  exact initial_completion metadata

end
end Kriterion.ArgoMAC.ArithmeticSimulator
