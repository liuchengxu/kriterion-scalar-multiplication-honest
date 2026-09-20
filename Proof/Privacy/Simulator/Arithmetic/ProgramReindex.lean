import Proof.Privacy.Simulator.SimulatorRuntime

namespace Kriterion.ArgoMAC.Security.SimulatorMachine
open Cryptography OperationalOracle

/-- The mapper changes query and answer encodings without changing the query budget. -/
def Program.reindex {source target : OracleSpec.{0, 0}}
    (request : source.Query → target.Query)
    (answer : (query : source.Query) → target.Answer (request query) → source.Answer query)
    {A : Type} {budget : Nat} : Program source A budget → Program target A budget
  | .pure value => .pure value
  | .query req next => .query (request req) (fun value => (next (answer req value)).reindex request answer)
  | .map f program => .map f (program.reindex request answer)
  | .bind program next => .bind (program.reindex request answer) (fun value => (next value).reindex request answer)
  | .weaken program bound => .weaken (program.reindex request answer) bound

/-- The mapped program executes the handler with the named answer encoding. -/
theorem Program.reindex_run {source target : OracleSpec.{0, 0}}
    (request : source.Query → target.Query)
    (answer : (query : source.Query) → target.Answer (request query) → source.Answer query)
    {A State : Type} {budget : Nat} (program : Program source A budget)
    (handler : OracleHandler target State) (state : State) :
    (program.reindex request answer).run handler state =
      program.run (fun query current =>
        let result := handler (request query) current
        (answer query result.1, result.2)) state := by
  induction program generalizing state with
  | pure => rfl
  | query query next ih => exact ih _ _
  | map f program ih => simp only [reindex, run, ih]
  | bind program next first second => simp only [reindex, run, first, second]
  | weaken program bound ih => exact ih state

/-- The mapped program preserves the complete sampled source law. -/
theorem Program.reindex_sampledLaw {source target : OracleSpec.{0, 0}}
    (request : source.Query → target.Query)
    (answer : (query : source.Query) → target.Answer (request query) → source.Answer query)
    {A State : Type} {budget : Nat} (program : Program source A budget)
    (draw : (query : target.Query) → State → Draw (target.Answer query × State)) (state : State) :
    (program.reindex request answer).sampledLaw draw state =
      program.sampledLaw (fun query current =>
        (draw (request query) current).map (fun result => (answer query result.1, result.2))) state := by
  induction program generalizing state with
  | pure => rfl
  | query query next ih =>
    simp only [reindex, sampledLaw, Draw.map_distribution, PMF.bind_map, ih, Function.comp_def]
  | map f program ih => simp only [reindex, sampledLaw, ih]
  | bind program next first second => simp only [reindex, sampledLaw, first, second]
  | weaken program bound ih => exact ih state

end Kriterion.ArgoMAC.Security.SimulatorMachine
