import Proof.Privacy.Transcript.OracleTranscript
import Security.AdaptivePrivacy

namespace Kriterion.ArgoMAC.Security

open Cryptography

universe u uAux

/-- This transcript contains only the public adaptive interaction. -/
structure AdaptiveTranscript (oracle : OracleSpec) (Input Public Labels : Type u) where
  publicTable : Public
  input : Input
  labels : Labels
  beforeEncode : List (Sigma oracle.Answer)
  afterEncode : List (Sigma oracle.Answer)
  decision : Bool

variable {oracle : OracleSpec}
  {Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle Topology State : Type u}
  {Aux : Type uAux}
  (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle)
  (randomTape : Nat → PMF Randomness) (realOracle : OracleHandler oracle Randomness)
  (topology : Circuit → Topology)
  (simulator : GarbledCircuit.Simulator Input Output Public Labels Topology State)
  (idealOracle : OracleHandler oracle State)
  (adversary : GarbledCircuit.AdaptiveAdversary oracle Input Public Labels Aux)
  (parameter : Nat) (circuit : Circuit) (auxiliary : Aux)

/-- The real transcript uses the actual garbling and encoding functions. -/
noncomputable def realAdaptiveTranscript : PMF (AdaptiveTranscript oracle Input Public Labels) :=
  (randomTape parameter).bind fun randomness =>
    let garbled := scheme.garble parameter circuit randomness
    (runOracleProgramWithTranscript realOracle
      (adversary.chooseInput parameter garbled.1 auxiliary) randomness).bind fun selected =>
        let labels := scheme.encode garbled.2 selected.1.1
        (runOracleProgramWithTranscript realOracle
          (adversary.decide parameter garbled.1 labels auxiliary selected.1.2) selected.2.1).map
            fun decided => ⟨garbled.1, selected.1.1, labels, selected.2.2,
              decided.2.2, decided.1⟩

/-- The ideal transcript uses the actual simulator distributions. -/
noncomputable def idealAdaptiveTranscript : PMF (AdaptiveTranscript oracle Input Public Labels) :=
  (simulator.simulateGarble parameter (topology circuit)).bind fun simulated =>
    (runOracleProgramWithTranscript idealOracle
      (adversary.chooseInput parameter simulated.1 auxiliary) simulated.2).bind fun selected =>
        (simulator.simulateEncode selected.2.1 selected.1.1
          (scheme.function circuit selected.1.1)).bind fun encoded =>
            (runOracleProgramWithTranscript idealOracle
              (adversary.decide parameter simulated.1 encoded.1 auxiliary selected.1.2)
              encoded.2).map fun decided =>
                ⟨simulated.1, selected.1.1, encoded.1, selected.2.2, decided.2.2, decided.1⟩

/-- The real transcript preserves the decision distribution. -/
theorem realAdaptiveTranscript_decision :
    (realAdaptiveTranscript scheme randomTape realOracle adversary parameter circuit auxiliary).map
        AdaptiveTranscript.decision =
      GarbledCircuit.realGame scheme randomTape realOracle adversary parameter circuit auxiliary := by
  simp only [realAdaptiveTranscript, GarbledCircuit.realGame, PMF.map_bind, PMF.map_comp]
  congr 1
  funext randomness
  rw [← runOracleProgramWithTranscript_erase realOracle
    (adversary.chooseInput parameter (scheme.garble parameter circuit randomness).1 auxiliary)
    randomness, PMF.bind_map]
  congr 1
  funext selected
  dsimp only [Function.comp_apply]
  rw [← runOracleProgramWithTranscript_erase realOracle, PMF.map_comp]
  rfl

/-- The ideal transcript preserves the decision distribution. -/
theorem idealAdaptiveTranscript_decision :
    (idealAdaptiveTranscript scheme topology simulator idealOracle adversary parameter circuit
        auxiliary).map AdaptiveTranscript.decision =
      GarbledCircuit.idealGame scheme topology simulator idealOracle adversary parameter circuit
        auxiliary := by
  simp only [idealAdaptiveTranscript, GarbledCircuit.idealGame, PMF.map_bind, PMF.map_comp]
  congr 1
  funext simulated
  rw [← runOracleProgramWithTranscript_erase idealOracle
    (adversary.chooseInput parameter simulated.1 auxiliary) simulated.2, PMF.bind_map]
  congr 1
  funext selected
  dsimp only [Function.comp_apply]
  congr 1
  funext encoded
  rw [← runOracleProgramWithTranscript_erase idealOracle, PMF.map_comp]
  rfl

end Kriterion.ArgoMAC.Security
