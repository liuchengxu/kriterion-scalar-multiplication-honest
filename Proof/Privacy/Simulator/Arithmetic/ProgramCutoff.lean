import Proof.Privacy.Simulator.Arithmetic.AdaptiveCutoff
import Proof.Privacy.Simulator.SimulatorRuntime

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security.SimulatorMachine
noncomputable section

/-- Two successive cutoff continuations preserve the first absent result. -/
theorem bindCutoff_assoc {A B C : Type} (source : PMF (Option A))
    (first : A → PMF (Option B)) (second : B → PMF (Option C)) :
    bindCutoff (bindCutoff source first) second = bindCutoff source (fun value => bindCutoff (first value) second) := by
  simp only [bindCutoff, PMF.bind_bind]
  congr 1
  funext result
  cases result <;> simp only [PMF.pure_bind]

/-- A budget cast does not change the cutoff source. -/
theorem sampledCutoff_cast {oracle : OracleSpec} {A State : Type}
    (handler : ∀ query, State → PMF (Option (oracle.Answer query × State))) {first second : Nat}
    (same : first = second) (program : OracleProgram oracle A first) (state : State) :
    runSampledCutoff handler (Security.ThreePhase.castBudget same program) state = runSampledCutoff handler program state := by
  cases same
  rfl

/-- An unused query allowance does not change the cutoff source. -/
theorem sampledCutoff_raise {oracle : OracleSpec} {A State : Type}
    (handler : ∀ query, State → PMF (Option (oracle.Answer query × State))) {budget : Nat}
    (extra : Nat) (program : OracleProgram oracle A budget) (state : State) :
    runSampledCutoff handler (Security.ThreePhase.raise extra program) state = runSampledCutoff handler program state := by
  induction program generalizing state with
  | pure => simp only [Security.ThreePhase.raise, runSampledCutoff]
  | query query next ih => simp only [Security.ThreePhase.raise, sampledCutoff_cast, runSampledCutoff, ih]
  | sample distribution next ih => simp only [Security.ThreePhase.raise, runSampledCutoff, ih]

/-- Appended programs retain the exact cutoff order and full source state. -/
theorem sampledCutoff_append {oracle : OracleSpec} {A B State : Type}
    (handler : ∀ query, State → PMF (Option (oracle.Answer query × State))) {first second : Nat}
    (source : OracleProgram oracle A first) (next : A → OracleProgram oracle B second) (state : State) :
    runSampledCutoff handler (Security.ThreePhase.append next source) state =
      bindCutoff (runSampledCutoff handler source state)
        (fun result => runSampledCutoff handler (next result.1) result.2) := by
  induction source generalizing state with
  | pure => simp only [Security.ThreePhase.append, sampledCutoff_cast, runSampledCutoff,
      sampledCutoff_raise, bindCutoff, PMF.bind_map, Function.comp_def]
  | query query branch ih =>
      simp only [Security.ThreePhase.append, sampledCutoff_cast, runSampledCutoff, ih, bindCutoff_assoc]
  | sample distribution branch ih =>
      simp only [Security.ThreePhase.append, runSampledCutoff, ih, bindCutoff, PMF.bind_bind]

end
end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.Security.SimulatorMachine
open Cryptography ArgoMAC.ArithmeticSimulator
noncomputable section

/-- The structural interpreter accepts any charged source handler with visible cutoff failure. -/
def Program.cutoffLaw {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (handler : ∀ query, State → PMF (Option (oracle.Answer query × State))) :
    Program oracle A budget → State → PMF (Option (A × State))
  | .pure value, state => PMF.pure (some (value, state))
  | .query request next, state => bindCutoff (handler request state)
      (fun result => (next result.1).cutoffLaw handler result.2)
  | .map convert source, state => (source.cutoffLaw handler state).map
      (Option.map fun result => (convert result.1, result.2))
  | .bind source next, state => bindCutoff (source.cutoffLaw handler state)
      (fun result => (next result.1).cutoffLaw handler result.2)
  | .weaken source _, state => source.cutoffLaw handler state

/-- The structural cutoff interpreter has the exact existing OracleProgram semantics. -/
theorem Program.cutoffLaw_toOracle {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (handler : ∀ query, State → PMF (Option (oracle.Answer query × State)))
    (program : Program oracle A budget) (state : State) :
    runSampledCutoff handler program.toOracle state = program.cutoffLaw handler state := by
  induction program generalizing state with
  | pure => simp only [toOracle, runSampledCutoff, PMF.pure_map, cutoffLaw]
  | query query next ih => simp only [toOracle, runSampledCutoff, cutoffLaw, ih]
  | map f source ih =>
      simp only [toOracle, sampledCutoff_cast, sampledCutoff_append, ih, cutoffLaw, runSampledCutoff, PMF.pure_map]
      unfold bindCutoff
      change PMF.bind _ _ = PMF.bind _ _
      congr 1
      funext result
      cases result <;> rfl
  | bind source next first second =>
      simp only [toOracle, sampledCutoff_append, first, second, cutoffLaw]
  | weaken source bounded ih => simp only [toOracle, sampledCutoff_cast, sampledCutoff_raise, ih, cutoffLaw]

end
end Kriterion.ArgoMAC.Security.SimulatorMachine
