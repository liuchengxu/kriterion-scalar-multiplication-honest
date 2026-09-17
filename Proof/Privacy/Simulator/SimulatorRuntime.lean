import Proof.Privacy.Simulator.SimulatorProtocol
import Proof.Privacy.Simulator.OperationalOracleLaw
import Proof.Privacy.Simulator.SamplingCutoff

namespace Kriterion.ArgoMAC.Security
open Cryptography OperationalOracle
namespace SimulatorMachine

/-- This interpreter obtains at most one bounded integer from its random source. -/
def runDraw {A Seed : Type}
    (random : (size : Nat) → 0 < size → Seed → Fin size × Seed) :
    Draw A → Seed → A × Seed
  | .pure value, seed => (value, seed)
  | .uniform size positive next, seed =>
      let sampled := random size positive seed
      (next sampled.1, sampled.2)

/-- The executable handler threads the random source through each sparse oracle operation. -/
def randomHandler {oracle : OracleSpec.{0, 0}} {State Seed : Type}
    (sparse : (query : oracle.Query) → State → Draw (oracle.Answer query × State))
    (random : (size : Nat) → 0 < size → Seed → Fin size × Seed) :
    OracleHandler oracle (State × Seed) := fun query state =>
  let answer := runDraw random (sparse query state.1) state.2
  (answer.1.1, answer.1.2, answer.2)

/-- The executable simulator program uses only the sparse handler and the random source. -/
def Program.execute {oracle : OracleSpec.{0, 0}} {A State Seed : Type} {budget : Nat}
    (sparse : (query : oracle.Query) → State → Draw (oracle.Answer query × State))
    (random : (size : Nat) → 0 < size → Seed → Fin size × Seed)
    (program : Program oracle A budget) (state : State) (seed : Seed) : A × State × Seed :=
  program.run (randomHandler sparse random) (state, seed)

/-- The probability semantics samples exactly the integer draws in the executable handler. -/
noncomputable def Program.sampledLaw {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (sparse : (query : oracle.Query) → State → Draw (oracle.Answer query × State)) :
    Program oracle A budget → State → PMF (A × State)
  | .pure value, state => PMF.pure (value, state)
  | .query request next, state => (sparse request state).distribution.bind fun answer =>
      (next answer.1).sampledLaw sparse answer.2
  | .map f source, state => (source.sampledLaw sparse state).map fun answer => (f answer.1, answer.2)
  | .bind source next, state => (source.sampledLaw sparse state).bind fun answer =>
      (next answer.1).sampledLaw sparse answer.2
  | .weaken source _, state => source.sampledLaw sparse state

private theorem sampled_cast {oracle : OracleSpec} {A State : Type}
    (handler : ∀ query, State → PMF (oracle.Answer query × State)) {first second : Nat}
    (same : first = second) (program : OracleProgram oracle A first) (state : State) :
    runSampled handler (ThreePhase.castBudget same program) state = runSampled handler program state := by
  cases same
  rfl

theorem sampled_raise {oracle : OracleSpec} {A State : Type}
    (handler : ∀ query, State → PMF (oracle.Answer query × State)) {budget : Nat}
    (extra : Nat) (program : OracleProgram oracle A budget) (state : State) :
    runSampled handler (ThreePhase.raise extra program) state = runSampled handler program state := by
  induction program generalizing state with
  | pure => simp only [ThreePhase.raise, runSampled]
  | query query next ih => simp only [ThreePhase.raise, sampled_cast, runSampled, ih]
  | sample distribution next ih => simp only [ThreePhase.raise, runSampled, ih]

theorem sampled_append {oracle : OracleSpec} {A B State : Type}
    (handler : ∀ query, State → PMF (oracle.Answer query × State)) {first second : Nat}
    (source : OracleProgram oracle A first) (next : A → OracleProgram oracle B second) (state : State) :
    runSampled handler (ThreePhase.append next source) state =
      (runSampled handler source state).bind fun answer => runSampled handler (next answer.1) answer.2 := by
  induction source generalizing state with
  | pure => simp only [ThreePhase.append, sampled_cast, runSampled, sampled_raise, PMF.bind_map,
      Function.comp_def]
  | query query branch ih => simp only [ThreePhase.append, sampled_cast, runSampled, ih, PMF.bind_bind]
  | sample distribution branch ih => simp only [ThreePhase.append, runSampled, ih, PMF.bind_bind]

/-- The executable syntax has the distribution used by the sparse oracle coupling theorem. -/
theorem Program.sampledLaw_toOracle {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (sparse : (query : oracle.Query) → State → Draw (oracle.Answer query × State))
    (program : Program oracle A budget) (state : State) :
    runSampled (fun query state => (sparse query state).distribution) program.toOracle state =
      program.sampledLaw sparse state := by
  induction program generalizing state with
  | pure => simp only [toOracle, runSampled, PMF.pure_map, sampledLaw]
  | query query next ih => simp only [toOracle, runSampled, sampledLaw, ih]
  | map f source ih =>
      simp only [toOracle, sampled_cast, sampled_append, ih, runSampled, PMF.pure_map, sampledLaw]
      rfl
  | bind source next first second => simp only [toOracle, sampled_append, first, second, sampledLaw]
  | weaken source bounded ih => simp only [toOracle, sampled_cast, sampled_raise, ih, sampledLaw]

/-- The executable interpreter respects the checked oracle-operation budget. -/
theorem Program.execute_calls {oracle : OracleSpec.{0, 0}} {A State Seed : Type} {budget : Nat}
    (sparse : (query : oracle.Query) → State → Draw (oracle.Answer query × State))
    (random : (size : Nat) → 0 < size → Seed → Fin size × Seed)
    (program : Program oracle A budget) (state : State) (seed : Seed) :
    (program.runCount (randomHandler sparse random) (state, seed)).1 =
        program.execute sparse random state seed ∧
      (program.runCount (randomHandler sparse random) (state, seed)).2 ≤ budget :=
  Program.runCount_correct _ _ _

end SimulatorMachine
end Kriterion.ArgoMAC.Security
