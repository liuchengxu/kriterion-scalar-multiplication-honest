import Proof.Privacy.Source.SmallSourceRatio
import Proof.Privacy.Source.Valid.ValidEndpointRatio
import Proof.Privacy.Source.Invalid.InvalidGhostEndpoint
import Proof.Privacy.AdaptiveSourceBound

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section

/-- The exact block cardinality gives the public source-ratio denominator. -/
theorem sourceRatio_blockCard [Fintype Block] (budget : Nat) (good real : ℝ≥0∞)
    (bound : (1 - ((186 * budget + 508 : Nat) : ℝ≥0∞) / Fintype.card Block) * good ≤ real) :
    (1 - ((186 * budget + 508 : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128) * good ≤ real := by
  have card : Fintype.card Block = 2 ^ 128 :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  simpa only [card, Nat.cast_pow, Nat.cast_ofNat] using bound

/-- The two input cases give the actual source ratio for every small query budget. -/
theorem concreteSmallSourceRatio [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)
    (witness : Garbling.Randomness)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100)
    (transcript : FullGateTranscript adversary.State) :
    (1 - (((186 * (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) + 508 : Nat) : ℝ≥0∞) /
      (2 : ℝ≥0∞) ^ 128)) *
      sourceGoodMass
        (fullGateGhostSamples adversary parameter auxiliary scalar.value witness
          (fullGateRealFallback adversary parameter auxiliary scalar witness))
        (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin} transcript ≤
      (realAdaptiveTranscriptWithState (Garbling.garbledCircuit construction)
        (randomTape witness) Garbling.oracleHandler adversary parameter scalar auxiliary) transcript := by
  classical
  by_cases zero : sourceGoodMass
      (fullGateGhostSamples adversary parameter auxiliary scalar.value witness
        (fullGateRealFallback adversary parameter auxiliary scalar witness))
      (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin} transcript = 0
  · rw [zero, mul_zero]
    exact bot_le
  obtain ⟨referenceBefore, referenceAfter, nonfixedWitness, key,
    firstCompatible, secondCompatible, nonfixed, bounded, bits, mac⟩ :=
    fullGateGhostGood_sourceFacts adversary parameter auxiliary scalar.value witness
      (fullGateRealFallback adversary parameter auxiliary scalar witness) transcript zero
  rcases transcript with ⟨table, selected, before, labels, decision, after⟩
  apply sourceRatio_blockCard
  by_cases valid : OnCurve selected.1
  · exact validGhostEndpoint_mass_ge adversary parameter auxiliary scalar witness
      (fullGateRealFallback adversary parameter auxiliary scalar witness) table
      referenceBefore referenceAfter selected labels decision before after key valid bits mac
      firstCompatible secondCompatible _ small bounded
  · exact invalidGhostEndpoint_mass_ge adversary parameter auxiliary scalar witness nonfixedWitness
      (fullGateRealFallback adversary parameter auxiliary scalar witness) table
      referenceBefore referenceAfter selected labels decision before after key valid bits mac
      firstCompatible secondCompatible nonfixed _ small bounded

/-- The concrete source ratio proves the universal 100-bit privacy bound. -/
theorem concreteAdaptivePrivacy [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type} (witness : Garbling.Randomness) :
    GarbledCircuit.ConcreteAdaptivePrivacy (Aux := Aux) (Garbling.garbledCircuit construction)
      Garbling.topology concreteCircuitSimulator (randomTape witness) Garbling.oracleHandler
      circuitSimulatorOracleHandler 100 := by
  letI : Fintype Block := Fintype.ofFinite Block
  apply concreteAdaptivePrivacy_of_smallSourceRatios witness
  intro adversary parameter scalar auxiliary small transcript
  exact concreteSmallSourceRatio adversary parameter scalar auxiliary witness small transcript

end
end Kriterion.ArgoMAC.Security
