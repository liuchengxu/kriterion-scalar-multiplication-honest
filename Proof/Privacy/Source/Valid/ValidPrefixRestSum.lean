import Proof.Privacy.Source.Valid.ValidPrefixPhaseWeight
import Proof.Privacy.Source.RandomTapeSourceSum

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable instFintypeInputMacKey_proof_3

set_option maxRecDepth 4096 in
/-- The original tape weight sum has the exact valid event phase factor. -/
def validOriginalWeight_phase_sum [FieldCertificate] [GroupCertificate]
    [blockFinite : Fintype Block] [tagFinite : Fintype FullCircuitSource] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (table : Pipeline.Table) (referenceBefore referenceAfter : SimulatorState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (key : InputMacKey)
    (valid : OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) := by
  have split := randomTape_fullTag_weighted witness parameter
    (validPrefixPhaseWeight adversary parameter auxiliary scalar fallback
      (table, selected, before, labels, decision, after))
  have phases := validPrefixPhaseWeight_sum adversary parameter auxiliary scalar witness fallback table
    referenceBefore referenceAfter selected labels decision before after key valid bits mac
    firstCompatible secondCompatible
  exact split.trans phases

end
end Kriterion.ArgoMAC.Security
