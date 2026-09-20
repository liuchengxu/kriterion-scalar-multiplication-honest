import Proof.Privacy.Simulator.Arithmetic.OracleFamilySource
import Proof.Privacy.Simulator.OperationalFamilyLaw
import Proof.Privacy.Simulator.OperationalHashLaw
import Proof.Privacy.Simulator.OperationalCompositionLaw

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle
noncomputable section

/-- The family accepts permutation reads, permutation programs, and hash reads. -/
abbrev oracleFamilySpec : OracleSpec :=
  sumSpec (familySpec (Fin 15748) (2 ^ 128)) (hashSpec BN254.BaseField (2 ^ 256))

/-- The family draws only from the selected finite source. -/
def oracleFamilyDraw (query : oracleFamilySpec.Query) (state : SparseOracleFamily) :
    Draw (oracleFamilySpec.Answer query × SparseOracleFamily) :=
  match query with
  | .inl request => (familyDraw request state.permutations).map
      (fun result => (result.1, {state with permutations := result.2}))
  | .inr key => (state.hash.query (by decide) key).map
      (fun result => (result.1, state.updateHash result.2))

/-- The sampled interpreter retains the complete finite source state. -/
def oracleFamilySampled (query : oracleFamilySpec.Query) (state : SparseOracleFamily) :
    PMF (oracleFamilySpec.Answer query × SparseOracleFamily) := (oracleFamilyDraw query state).distribution

/-- The eager state retains every conditional permutation and the conditional hash function. -/
abbrev OracleFamilyEager :=
  (Fin 15748 → ProgrammedPermutation (2 ^ 128) × Equiv.Perm (Fin (2 ^ 128))) ×
    (HashTable BN254.BaseField (2 ^ 256) × (BN254.BaseField → Fin (2 ^ 256)))

/-- The eager interpreter changes exactly the selected oracle component. -/
def oracleFamilyEager : OracleHandler oracleFamilySpec OracleFamilyEager := sumEager familyEager hashEager

/-- The completion kernel preserves the source state's conditional correlations. -/
def oracleFamilyCompletion (state : SparseOracleFamily) : PMF OracleFamilyEager :=
  productKernel familyCompletion (hashCompletion (by decide)) (state.permutations, state.hash)

/-- Every finite family query has the same joint conditional law as the eager query. -/
theorem oracleFamily_step (query : oracleFamilySpec.Query) (state : SparseOracleFamily) :
    (oracleFamilyCompletion state).map (oracleFamilyEager query) =
      (oracleFamilySampled query state).bind (fun result =>
        (oracleFamilyCompletion result.2).map (fun eager => (result.1, eager))) := by
  have law := productKernel_step familyEager hashEager familySampled (hashSampled (by decide))
    familyCompletion (hashCompletion (by decide)) family_step (hash_step (by decide)) query
    (state.permutations, state.hash)
  cases query with
  | inl request =>
      simpa only [oracleFamilyCompletion, oracleFamilyEager, oracleFamilySampled, oracleFamilyDraw,
        Draw.map_distribution, familyDraw_distribution, sumSampled, PMF.bind_map, Function.comp_def] using law
  | inr key =>
      simpa only [oracleFamilyCompletion, oracleFamilyEager, oracleFamilySampled, oracleFamilyDraw,
        Draw.map_distribution, sumSampled, hashSampled, PMF.bind_map, Function.comp_def,
        SparseOracleFamily.updateHash] using law

/-- Every adaptive source program preserves the complete eager conditional law. -/
theorem oracleFamily_adaptive_joint {Result : Type} {budget : Nat}
    (program : OracleProgram oracleFamilySpec Result budget) (state : SparseOracleFamily) :
    (oracleFamilyCompletion state).bind (fun eager => program.run oracleFamilyEager eager) =
      (runSampled oracleFamilySampled program state).bind (fun result =>
        (oracleFamilyCompletion result.2).map (fun eager => (result.1, eager))) :=
  adaptive_joint_law oracleFamilyEager oracleFamilySampled oracleFamilyCompletion oracleFamily_step program state

end
end Kriterion.ArgoMAC.ArithmeticSimulator
