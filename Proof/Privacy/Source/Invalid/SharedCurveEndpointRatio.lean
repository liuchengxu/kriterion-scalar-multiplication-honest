import Proof.Privacy.Source.Invalid.SharedCurveGlobalEventRatio
import Proof.Privacy.Source.SharedRealEndpointPhaseMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance sharedCurveEndpointGateDecidableEq : DecidableEq RawCircuitGate := fun a b => FinEnum.decEq a b
local instance sharedCurveEndpointKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance sharedCurveEndpointKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
attribute [local irreducible] PMF.uniformOfFintype
set_option maxRecDepth 2048

/-- The guarded shared curve source preserves both adaptive program factors. -/
theorem sharedCurveEndpoint_mass_ge [FieldCertificate] [GroupCertificate] [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (table : Pipeline.Table) (referenceBefore referenceAfter : Shared.Simulator.OracleState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (key : InputMacKey)
    (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after)
    (initial : GarblingSourceRest → Shared.Simulator.OracleState)
    (empty : ∀ rest, (initial rest).fixedTranscript = [])
    (enc : ∀ rest, (initial rest).encOracle = rest.encPRFOracle)
    (valid : ∀ rest, SimulatorInvariant (initial rest))
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : (before ++ after).length ≤ budget) :
    letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
    let phase :=
      ((runOracleProgramWithTranscript idealOracleHandler
        (adversary.chooseInput parameter table auxiliary) referenceBefore).map
          (fun output => (output.1, output.2.2))) (selected, before) *
      ((runOracleProgramWithTranscript idealOracleHandler
        (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
          (fun output => (output.1, output.2.2))) (decision, after)
    ((1 - ((54691280 + 368 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128) *
      encTranscriptFactor (encOracleTranscriptRecords (sharedLegacyTranscript (before ++ after)))) *
        (phase * ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
          sharedCurvePrefixEventMass rest
            (FieldMacToECMac.outputKeys construction scalar.value rest.reference.offsets)
            table selected.1 key (initial rest) before after) ≤
      (realAdaptiveTranscriptWithState sharedInternalCircuit
        (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary)
          (table, selected, before, labels, decision, after) := by
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  dsimp only
  rw [sharedRealAdaptiveTranscript_retained_factor adversary parameter auxiliary scalar witness table
    referenceBefore referenceAfter selected labels decision before after key bits mac firstCompatible secondCompatible]
  rw [mul_left_comm]
  apply mul_le_mul_right
  exact sharedCurvePrefixEventMass_global_ratio witness parameter
    (fun rest => FieldMacToECMac.outputKeys construction scalar.value rest.reference.offsets)
    (fun _ _ _ => rfl) table selected.1 key initial before after empty enc valid budget small lengthBound

end
end Kriterion.ArgoMAC.Security
