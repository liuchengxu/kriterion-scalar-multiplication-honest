import Proof.Privacy.Simulator.Arithmetic.ProgramReindex
import Proof.Privacy.Simulator.Arithmetic.ParsedProgramSource

namespace Kriterion.ArgoMAC.Security.SimulatorMachine
open Cryptography ArgoMAC.ArithmeticSimulator
noncomputable section

/-- The reindexed program preserves every accepted reply and cutoff branch. -/
theorem Program.reindex_cutoffLaw {source target : OracleSpec.{0, 0}}
    (request : source.Query → target.Query)
    (answer : (query : source.Query) → target.Answer (request query) → source.Answer query)
    {A State : Type} {budget : Nat} (program : Program source A budget)
    (handler : ∀ query, State → PMF (Option (target.Answer query × State))) (state : State) :
    (program.reindex request answer).cutoffLaw handler state =
      program.cutoffLaw (fun query current => (handler (request query) current).map
        (Option.map fun result => (answer query result.1, result.2))) state := by
  induction program generalizing state with
  | pure => rfl
  | query query next ih =>
      simp only [reindex, cutoffLaw, bindCutoff, PMF.bind_map]
      apply congrArg (PMF.bind (handler (request query) state))
      funext result
      cases result with
      | none => rfl
      | some result => exact ih _ _
  | map convert program ih => simp only [reindex, cutoffLaw, ih]
  | bind program next first second => simp only [reindex, cutoffLaw, first, second]
  | weaken program bound ih => exact ih state

/-- A state decoder commutes with the complete program when it commutes with every query. -/
theorem Program.cutoffLaw_decode {oracle : OracleSpec.{0, 0}} {A State Source : Type} {budget : Nat}
    (program : Program oracle A budget)
    (handler : ∀ query, State → PMF (Option (oracle.Answer query × State)))
    (source : ∀ query, Source → PMF (Option (oracle.Answer query × Source)))
    (decode : State → Source)
    (same : ∀ request state,
      (handler request state).map (Option.map fun result => (result.1, decode result.2)) = source request (decode state))
    (state : State) :
    (program.cutoffLaw handler state).map (Option.map fun result => (result.1, decode result.2)) =
      program.cutoffLaw source (decode state) := by
  rw [← Program.cutoffLaw_toOracle, ← Program.cutoffLaw_toOracle]
  exact runSampledCutoff_decode handler source decode (fun _ => True)
    (fun request state _ => same request state) (by intros; trivial) program.toOracle state trivial

end
end Kriterion.ArgoMAC.Security.SimulatorMachine
