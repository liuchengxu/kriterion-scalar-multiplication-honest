import Proof.Privacy.Source.Valid.ValidNamedSourceRatio
import Proof.Privacy.Source.Valid.ValidPrefixNormalization
import Proof.Privacy.Source.SourcePrefixReference

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
  fixedQueryDomainFintype transcriptOracleFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The checked event laws identify the compatible retained tag sum. -/
def validRestEventSum_eq [fieldCert : FieldCertificate] [groupCert : GroupCertificate]
    [blockFinite : Fintype Block]
    (reference : SimulatorState) (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (nonfixed : NonFixedTranscriptCompatible rest.reference (before ++ after)) :=
  let split := (nonFixedTranscriptCompatible_append rest.reference before after).mp nonfixed
  tsum_congr (L := .unconditional _) (fun tag => @validTagGoodEvent_weighted_mass fieldCert groupCert blockFinite
    rest outputKeys table input key (sourcePrefixReference reference rest) before after tag rfl rfl rfl
    (sourcePrefixReference_compatible reference rest before compatible split.1) split.2
    (sourcePrefixReference_oracleExists reference rest before compatible))

/-- The incompatible retained tag sum has zero mass. -/
def validRestEventSum_zero [fieldCert : FieldCertificate] [groupCert : GroupCertificate]
    [blockFinite : Fintype Block]
    (reference : SimulatorState) (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (incompatible : ¬NonFixedTranscriptCompatible rest.reference (before ++ after)) :=
  ENNReal.tsum_eq_zero.mpr (fun tag => (congrArg (((PMF.uniformOfFintype FullCircuitSource) tag) * ·)
    (@validTagGoodEvent_mass_zero fieldCert groupCert blockFinite rest outputKeys table input key
      (sourcePrefixReference reference rest) before after tag rfl rfl incompatible)).trans (by simp only [mul_zero]))

/-- The zero cases identify the whole event sum with its compatible subtype sum. -/
theorem weightedEventSubtype_eq {Source : Type}
    (weights : Source → ℝ≥0∞) (kept : Source → Prop)
    (eventMass : Source → ℝ≥0∞) (sourceMass : Source → ℝ≥0∞)
    (goodEq : ∀ source, kept source → eventMass source = sourceMass source)
    (badZero : ∀ source, ¬kept source → eventMass source = 0) :
    (∑' source, weights source * eventMass source) =
      ∑' source : {source // kept source}, weights source.1 * sourceMass source.1 := by
  classical
  calc
    _ = ∑' source, ({source | kept source}.indicator (fun source => weights source * eventMass source) source) := tsum_congr (fun source => by
      by_cases good : kept source <;> simp [Set.indicator, good, badZero])
    _ = ∑' source : {source // kept source}, weights source.1 * eventMass source.1 :=
      (tsum_subtype {source | kept source} (fun source => weights source * eventMass source)).symm
    _ = _ := tsum_congr (fun source => congrArg (weights source.1 * ·) (goodEq source.1 source.2))

set_option maxRecDepth 4096 in
/-- The complete valid event sum has the actual random-tape lower bound. -/
def validEventSourceSum_real_le
    [fieldCert : FieldCertificate] [groupCert : GroupCertificate] [blockFinite : Fintype Block]
    (witness : Garbling.Randomness) (parameter : Nat)
    (reference : SimulatorState) (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (valid : OnCurve input)
    (queries : Nat) (small : queries < 2 ^ 100) (lengthBound : (before ++ after).length ≤ queries) :=
  letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
  let sourceEq := weightedEventSubtype_eq
    (fun rest : GarblingSourceRest => (PMF.uniformOfFintype GarblingSourceRest) rest)
    (fun rest => NonFixedTranscriptCompatible rest.reference (before ++ after)) _ _
    (fun rest nonfixed => @validRestEventSum_eq fieldCert groupCert blockFinite reference rest (outputKeys rest)
      table input key before after compatible nonfixed)
    (fun rest bad => by
      simpa only [PMF.uniformOfFintype_apply] using
        (@validRestEventSum_zero fieldCert groupCert blockFinite reference rest (outputKeys rest)
          table input key before after bad))
  le_trans (le_of_eq (congrArg
    ((1 - (182 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞)) * ·) sourceEq))
    (@validGlobalSourceMass_named_le fieldCert groupCert blockFinite witness parameter outputKeys table input key
      (fun rest => transcriptFinalState idealOracleHandler (sourcePrefixReference reference rest) before)
      before after (fun rest => sourcePrefixReference_oracleExists reference rest before compatible) valid
      (fun rest => sourcePrefixReference_members reference rest before compatible) queries small lengthBound)

end
end Kriterion.ArgoMAC.Security
