import Proof.Privacy.Source.Invalid.InvalidRestPhaseSum
import Proof.Privacy.Source.SourceRestRefresh
import Proof.Privacy.Source.Invalid.InvalidEventAverage
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
variable [Nonempty InputMacKey] [Nonempty FullCircuitSource]
  [Fintype FullCircuitSource]
  [Fintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)]

/-- This mass keeps the exact invalid event under the original retained source. -/
def invalidRestEventMass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (scalar : ScalarField) (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (rest : GarblingSourceRest) : ℝ≥0∞ :=
    ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
      if rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after) then
        (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
          (invalidTagGoodEvent rest (outputKeys construction scalar rest.reference.offsets)
            table input key (sourcePrefixReference reference rest) before after tag) else 0

/-- The normalized source admits an independent refresh of both nonfixed functions. -/
theorem invalidRestEventMass_refresh [FieldCertificate] [GroupCertificate] [Fintype Block]
    [Nonempty GarblingSourceRest]
    (scalar : ScalarField) (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer)) :
    (∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      ∑' nonfixed : (PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle,
        (PMF.uniformOfFintype ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle)) nonfixed *
          invalidRestEventMass scalar table input key reference before after
            {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2}) =
      ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
        invalidRestEventMass scalar table input key reference before after rest :=
  sourceRest_nonfixed_refresh _

omit [Nonempty InputMacKey] [Nonempty FullCircuitSource]
  [Fintype FullCircuitSource]
  [Fintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)] in
private theorem guarded_average_swap {Tag Sample : Type*} (tags : PMF Tag) (samples : PMF Sample)
    (guard : Prop) {guardDec : Decidable guard} (weight : Tag → Sample → ℝ≥0∞) :
    (∑' sample, samples sample * ∑' tag, tags tag * @ite ℝ≥0∞ guard guardDec (weight tag sample) 0) =
      ∑' tag, tags tag * @ite ℝ≥0∞ guard guardDec (∑' sample, samples sample * weight tag sample) 0 := by
  by_cases kept : guard
  · simp only [kept, if_true, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro tag
    apply tsum_congr
    intro sample
    ac_rfl
  · simp only [kept, if_false, mul_zero, tsum_zero]


set_option maxRecDepth 4096 in
/-- The updated source has the exact updated event reference. -/
theorem invalidRestEventMass_updated [FieldCertificate] [GroupCertificate] [Fintype Block]
    (scalar : ScalarField) (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (rest : GarblingSourceRest) (enc : PermutationOracle EncPRF.PermutationIndex Block)
    (hash : EncPRF.HashOracle) :
    invalidRestEventMass scalar table input key reference before after
      {rest with encPRFOracle := enc, hashOracle := hash} =
    ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
      if rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after) then
        (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
          (invalidTagGoodEvent {rest with encPRFOracle := enc, hashOracle := hash}
            (outputKeys construction scalar rest.reference.offsets) table input key
            {sourcePrefixReference reference rest with encOracle := enc, hashOracle := hash}
            before after tag) else 0 := by
  unfold invalidRestEventMass
  apply tsum_congr
  intro tag
  apply congrArg (_ * ·)
  apply congrArg (fun mass : ℝ≥0∞ => if rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after) then mass else 0)
  apply congrArg (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
  rfl

omit [Nonempty InputMacKey] [Nonempty FullCircuitSource]
  [Fintype FullCircuitSource]
  [Fintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)] in
private theorem refreshed_average {Tag Sample : Type*} (tags : PMF Tag) (samples : PMF Sample)
    (guard : Prop) {guardDec : Decidable guard} (weight : Tag → Sample → ℝ≥0∞) (mass : Sample → ℝ≥0∞)
    (point : ∀ sample, mass sample = ∑' tag, tags tag * @ite ℝ≥0∞ guard guardDec (weight tag sample) 0) :
    (∑' sample, samples sample * mass sample) =
      ∑' tag, tags tag * @ite ℝ≥0∞ guard guardDec (∑' sample, samples sample * weight tag sample) 0 := by
  exact (tsum_congr fun sample => congrArg (samples sample * ·) (point sample)).trans
    (guarded_average_swap tags samples guard weight)

omit [Nonempty InputMacKey] [Nonempty FullCircuitSource]
  [Fintype FullCircuitSource]
  [Fintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)] in
private theorem refreshed_double_average {Tag First Second : Type*}
    [Fintype First] [Fintype Second] [Nonempty First] [Nonempty Second]
    (tags : PMF Tag) (guard : Prop) {guardDec : Decidable guard}
    (weight : Tag → First × Second → ℝ≥0∞) (mass : First × Second → ℝ≥0∞)
    (point : ∀ sample, mass sample = ∑' tag, tags tag * @ite ℝ≥0∞ guard guardDec (weight tag sample) 0) :
    (∑' sample, (PMF.uniformOfFintype (First × Second)) sample * mass sample) =
    ∑' tag, tags tag * @ite ℝ≥0∞ guard guardDec
      (∑' second, (PMF.uniformOfFintype Second) second *
        ∑' first, (PMF.uniformOfFintype First) first * weight tag (first, second)) 0 := by
  apply (refreshed_average tags (PMF.uniformOfFintype (First × Second)) guard
    weight mass point).trans
  apply tsum_congr
  intro tag
  apply congrArg (tags tag * ·)
  exact congrArg (fun value => @ite ℝ≥0∞ guard guardDec value 0)
    (uniform_pair_average_swap (fun first second => weight tag (first, second)))

set_option maxRecDepth 4096 in
/-- The refreshed source has the exact hash-then-Enc event average. -/
def invalidRestEventMass_refreshed [FieldCertificate] [GroupCertificate] [Fintype Block]
    [Fintype EncPRF.HashOracle] [Fintype (PermutationOracle EncPRF.PermutationIndex Block)]
    (scalar : ScalarField) (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (rest : GarblingSourceRest) :=
  refreshed_double_average (First := PermutationOracle EncPRF.PermutationIndex Block)
    (Second := EncPRF.HashOracle) (PMF.uniformOfFintype FullCircuitSource)
    (rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after)) _ _
    (fun nonfixed => invalidRestEventMass_updated scalar table input key reference before after rest nonfixed.1 nonfixed.2)

end
end Kriterion.ArgoMAC.Security
