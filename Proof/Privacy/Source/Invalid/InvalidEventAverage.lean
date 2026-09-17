import Proof.Privacy.Source.Invalid.InvalidEventNonfixed

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
  instDecidableEqRawCircuitGate_1 fixedQueryDomainFintype transcriptOracleFintype
attribute [local instance] instNonemptyInputMacKey_proof_8

/-- A uniform pair average equals the reversed nested uniform averages. -/
theorem uniform_pair_average_swap {First Second : Type*}
    [Fintype First] [Fintype Second] [Nonempty First] [Nonempty Second]
    (weight : First → Second → ℝ≥0∞) :
    (∑' pair, (PMF.uniformOfFintype (First × Second)) pair * weight pair.1 pair.2) =
      ∑' second, (PMF.uniformOfFintype Second) second *
        ∑' first, (PMF.uniformOfFintype First) first * weight first second := by
  rw [ENNReal.tsum_prod']
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro second
  apply tsum_congr
  intro first
  ac_rfl

private theorem double_average_congr {First Second : Type*} (first : PMF First) (second : PMF Second)
    {left right : First → Second → ℝ≥0∞} (pointwise : ∀ a b, left a b = right a b) :
    (∑' a, first a * ∑' b, second b * left a b) =
      ∑' a, first a * ∑' b, second b * right a b := by
  apply tsum_congr
  intro a
  apply congrArg (first a * ·)
  apply tsum_congr
  intro b
  exact congrArg (second b * ·) (pointwise a b)

set_option maxRecDepth 4096 in
/-- The normalized Enc and hash average keeps one actual source guard and one fixed program mass. -/
private def invalidTagGoodEvent_nonfixed_average_for [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource) (invalid : ¬ OnCurve input) (empty : initial.fixedTranscript = [])
    (initialEnc : initial.encOracle = rest.encPRFOracle) (initialHash : initial.hashOracle = rest.hashOracle)
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)]
    (hashSamples : PMF EncPRF.HashOracle)
    (encSamples : PMF (PermutationOracle EncPRF.PermutationIndex Block)) :=
  double_average_congr hashSamples encSamples
    (fun hash enc => invalidTagGoodEvent_mass_nonfixed_factor rest outputKeys table input key initial before after tag
      invalid empty initialEnc initialHash compatible enc hash)

set_option maxRecDepth 4096 in
/-- The normalized Enc and hash average keeps one actual source guard and one fixed program mass. -/
def invalidTagGoodEvent_nonfixed_average [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource) (invalid : ¬ OnCurve input) (empty : initial.fixedTranscript = [])
    (initialEnc : initial.encOracle = rest.encPRFOracle) (initialHash : initial.hashOracle = rest.hashOracle)
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :=
  invalidTagGoodEvent_nonfixed_average_for rest outputKeys table input key initial before after tag
    invalid empty initialEnc initialHash compatible
    (PMF.uniformOfFintype EncPRF.HashOracle)
    (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block))


end
end Kriterion.ArgoMAC.Security
