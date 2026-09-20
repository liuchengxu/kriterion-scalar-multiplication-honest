import Proof.Privacy.Transcript.SharedIdealTranscript
import Proof.Privacy.Source.SharedTranscriptMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- Every recorded shared prefix preserves the simulator invariant. -/
theorem sharedIdealTranscriptFinal_invariant (initial : Shared.Simulator.OracleState)
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (valid : SimulatorInvariant initial) :
    SimulatorInvariant (transcriptFinalState idealOracleHandler initial transcript) := by
  induction transcript generalizing initial with
  | nil => exact valid
  | cons entry tail ih =>
      exact ih _ (idealOracleHandler_preservesInvariant entry.1 initial valid)

/-- The final shared oracle witnesses the conditional prefix distribution. -/
theorem sharedIdealTranscriptFinal_nonempty (initial : Shared.Simulator.OracleState)
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (valid : SimulatorInvariant initial) :
    Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial transcript).fixedTranscript) :=
  ⟨⟨(transcriptFinalState idealOracleHandler initial transcript).fixedOracle,
    (sharedIdealTranscriptFinal_invariant initial transcript valid).1⟩⟩

end
end Kriterion.ArgoMAC.Security
