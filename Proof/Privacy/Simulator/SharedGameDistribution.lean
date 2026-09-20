import Proof.Privacy.Transcript.SharedIdealTranscript

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- The shared adaptive oracle run leaves the private circuit frame unchanged. -/
theorem sharedRunCircuitSimulatorWithTranscript {Result : Type*} {budget : Nat}
    (program : OracleProgram sharedRealOracleSpec Result budget) (state : Shared.Simulator.State) :
    runOracleProgramWithTranscript circuitSimulatorOracleHandler program state =
      (runOracleProgramWithTranscript idealOracleHandler program state.oracle).map
        (fun output => (output.1, {state with oracle := output.2.1}, output.2.2)) := by
  induction program generalizing state with
  | pure result =>
      simp only [runOracleProgramWithTranscript_pure, PMF.map_comp]
      rfl
  | query request next ih =>
      simp only [runOracleProgramWithTranscript_query, circuitSimulatorOracleHandler]
      rw [ih, PMF.map_comp, PMF.map_comp]
      rfl
  | sample distribution next ih =>
      simp only [runOracleProgramWithTranscript_sample, PMF.map_bind]
      congr 1
      funext value
      exact ih value state

/-- The shared circuit transcript updates only the recording oracle state. -/
theorem sharedCircuitTranscriptFinalState (state : Shared.Simulator.State)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    transcriptFinalState circuitSimulatorOracleHandler state transcript =
      {state with oracle := transcriptFinalState idealOracleHandler state.oracle transcript} := by
  induction transcript generalizing state with
  | nil => rfl
  | cons entry tail ih =>
      rcases entry with ⟨request, answer⟩
      simp only [transcriptFinalState, circuitSimulatorOracleHandler, ih]

/-- Both shared adaptive phases have the same law after the private-frame projection. -/
theorem sharedCircuitTwoPhaseTranscript_oracle {First Labels Second : Type}
    {firstBudget secondBudget : Nat}
    (choose : OracleProgram sharedRealOracleSpec First firstBudget)
    (encode : Shared.Simulator.State → First → PMF (Labels × Shared.Simulator.State))
    (decide : First → Labels → OracleProgram sharedRealOracleSpec Second secondBudget)
    (state : Shared.Simulator.State) :
    twoPhaseTranscript circuitSimulatorOracleHandler choose encode decide state =
      twoPhaseTranscript idealOracleHandler choose
        (fun oracle selected => (encode {state with oracle} selected).map
          (fun encoded => (encoded.1, encoded.2.oracle))) decide state.oracle := by
  simp only [twoPhaseTranscript, sharedRunCircuitSimulatorWithTranscript, PMF.bind_map,
    PMF.map_comp, Function.comp_def]

attribute [local instance] publicInputMacKeyFintype
local instance sharedGameKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance sharedGameSampleNonempty : Nonempty PublicSample := ⟨defaultSimulatorCoin.tableSample⟩
local instance sharedGameOracleNonempty : Nonempty (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) :=
  ⟨(⟨fun _ => Equiv.refl Block⟩, ⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0))⟩

/-- The shared offline tape has independent private coins for each fixed public oracle. -/
theorem sharedTape_bind {Observation : Type*} (parameter : Nat) (topology : Garbling.Topology)
    (observe : Shared.Simulator.State → PMF Observation) :
    (Shared.Simulator.tape parameter topology).bind observe =
      (PMF.uniformOfFintype (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind fun oracles =>
        (PMF.uniformOfFintype BaseField).bind fun bridge =>
          (PMF.uniformOfFintype InputMacKey).bind fun key =>
            (PMF.uniformOfFintype PublicSample).bind fun sample =>
              observe (Shared.Simulator.initialState (sample, key, bridge) oracles) := by
  have offline : SimulatorSampling.offline.law =
      (PMF.uniformOfFintype BaseField).bind fun bridge =>
        (PMF.uniformOfFintype InputMacKey).bind fun key =>
          (PMF.uniformOfFintype PublicSample).map fun sample => (sample, key, bridge) := by
    rw [SimulatorSampling.offline_uniform, uniform_prod_eq_bind, uniform_prod_eq_bind]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  simp only [Shared.Simulator.tape, offline, PMF.bind_bind, PMF.bind_map, Function.comp_def]

end
end Kriterion.ArgoMAC.Security
