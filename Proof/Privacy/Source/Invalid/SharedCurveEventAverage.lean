import Proof.Privacy.Source.Invalid.SharedCurveEventNonfixed

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
set_option maxRecDepth 2048
attribute [local irreducible] PMF.uniformOfFintype Shared.Simulator.commands
  sharedRetainedCurveCommands
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance curveAverageGateDecidableEq : DecidableEq RawCircuitGate := fun a b => FinEnum.decEq a b
local instance curveAverageKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveAverageKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

private theorem guardedAverage {A : Type*} (distribution : PMF A) (condition : A → Prop)
    (kept : Prop) [Decidable kept] [DecidablePred condition]
    (labels first second source phase : ENNReal) :
    (if kept then labels * (first * ∑' a, distribution a *
      if condition a then second * (source * phase) else 0) else 0) =
      (first * second) * source * ∑' a, distribution a *
        if condition a then (if kept then labels * phase else 0) else 0 := by
  by_cases good : kept
  · simp only [if_pos good, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro a
    by_cases matching : condition a
    · simp only [if_pos matching]
      ac_rfl
    · simp only [if_neg matching, mul_zero]
  · simp only [if_neg good, ite_self, mul_zero, tsum_zero]

/-- This factor contains both relative losses and the exact EncPRF transcript mass. -/
def sharedCurveRelativeFactor [Fintype Block] (budget historyLength : Nat)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) : ENNReal :=
  ((1 - ((4 * budget : Nat) : ENNReal) / Fintype.card Block) *
    encTranscriptFactor (encOracleTranscriptRecords (sharedLegacyTranscript transcript))) *
      (1 - ((54691280 + (364 * historyLength : Nat)) / (2 : ENNReal) ^ 128))

/-- The lower source mass is the exact hash-averaged two-phase curve event with its relative factor. -/
theorem sharedCurveTagLowerMass_event_average [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (tag : FullCircuitSource) (budget : Nat)
    (empty : initial.fixedTranscript = [])
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    (enc : initial.encOracle = rest.encPRFOracle)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    let reference := transcriptFinalState idealOracleHandler initial before
    (if SharedCurveTagGood rest keys table input key reference (before ++ after) tag then
      (Fintype.card (EncPRF.PermutationIndex → Block) : ENNReal)⁻¹ *
        sharedCurveTagLowerMass rest keys input key tag reference (sharedFixedTranscriptRecords after)
          (before ++ after) budget else 0) =
      sharedCurveRelativeFactor budget (reference.fixedTranscript ++ sharedFixedTranscriptRecords after).length
        (before ++ after) * (PMF.uniformOfFintype FullCircuitSource) tag *
          ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
            (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
              (sharedCurveTagEvent rest keys table input key {initial with hashOracle := hash} before after tag) := by
  dsimp only
  simp_rw [sharedCurveTagEvent_hash_mass rest keys table input key initial _ before after tag empty compatible]
  rw [sharedCurveRelativeFactor, sharedCurveTagLowerMass]
  rw [(sharedIdealTranscriptFinal_oracles initial before).1, ← enc]
  simpa only [mul_assoc] using guardedAverage (PMF.uniformOfFintype EncPRF.HashOracle)
    (fun hash => SharedNonFixedTranscriptCompatible (initial.fixedOracle, initial.encOracle, hash) (before ++ after))
    (SharedCurveTagGood rest keys table input key
      (transcriptFinalState idealOracleHandler initial before) (before ++ after) tag)
    ((Fintype.card (EncPRF.PermutationIndex → Block) : ENNReal)⁻¹)
    ((1 - ((4 * budget : Nat) : ENNReal) / Fintype.card Block) *
      encTranscriptFactor (encOracleTranscriptRecords (sharedLegacyTranscript (before ++ after))))
    (1 - ((54691280 + (364 * ((transcriptFinalState idealOracleHandler initial before).fixedTranscript ++
      sharedFixedTranscriptRecords after).length : Nat)) / (2 : ENNReal) ^ 128))
    ((PMF.uniformOfFintype FullCircuitSource) tag)
    (Shared.Simulator.transcriptMass (transcriptFinalState idealOracleHandler initial before).fixedTranscript *
      ((PMF.uniformOfFintype (TranscriptOracle
        (transcriptFinalState idealOracleHandler initial before).fixedTranscript)).map
          (fun oracle => Shared.Simulator.commands
            {transcriptFinalState idealOracleHandler initial before with fixedOracle := oracle.1}
            (sharedRetainedCurveCommands rest keys input key tag))).toOuterMeasure
              {programmed | PermutationTranscriptMatches programmed.fixedOracle (sharedFixedTranscriptRecords after)})

end
end Kriterion.ArgoMAC.Security
