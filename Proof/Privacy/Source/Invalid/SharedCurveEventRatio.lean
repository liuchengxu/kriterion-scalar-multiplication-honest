import Proof.Privacy.Source.Invalid.SharedCurveEventAverage

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance curveEventRatioGateDecidableEq : DecidableEq RawCircuitGate := fun a b => FinEnum.decEq a b
local instance curveEventRatioKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveEventRatioKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
set_option maxRecDepth 2048

/-- The complete two-phase curve-event source satisfies the shared real-source ratio. -/
theorem sharedCurveTagEvent_sum_ratio [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer))
    (empty : initial.fixedTranscript = [])
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    (enc : initial.encOracle = rest.encPRFOracle)
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : (before ++ after).length ≤ budget)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    let reference := transcriptFinalState idealOracleHandler initial before
    sharedCurveRelativeFactor budget (reference.fixedTranscript ++ sharedFixedTranscriptRecords after).length
      (before ++ after) *
      (∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
        ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
          (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
            (sharedCurveTagEvent rest keys table input key {initial with hashOracle := hash} before after tag)) ≤
      sharedRefreshedLinkedSourceMass rest keys table input (key.encodeAffine input) (before ++ after) := by
  dsimp only
  have bound := sharedCurveGoodTag_sum_le rest keys table input key
    (transcriptFinalState idealOracleHandler initial before) (sharedFixedTranscriptRecords after)
    (before ++ after) (sharedIdealTranscriptFinal_fullPermutation initial before after empty compatible)
    budget small lengthBound
  simp_rw [sharedCurveTagLowerMass_event_average rest keys table input key initial before after _ budget
    empty compatible enc] at bound
  simpa only [mul_assoc, ENNReal.tsum_mul_left] using bound

end
end Kriterion.ArgoMAC.Security
