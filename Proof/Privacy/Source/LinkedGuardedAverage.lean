import Proof.Privacy.Source.LinkedTagKeyMass
import Proof.Privacy.Source.GuardedAverage
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype instFintypeEncQueryDomainOfBlock
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

set_option maxRecDepth 2048 in
/-- The actual linked source bounds one guarded independent product event. -/
theorem actualLinkedTagKey_guarded_mass_ge [Fintype Block] [Fintype BaseField] [Fintype Pipeline.FixedKeyIndex]
    (outputKeys : OutputKeys) (pointRandomness : Randomness)
    (bridgeKey r1 r2 : BaseField) (mask : NonZeroBase) (randomness : Garbling.Randomness)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (selected : EncPRF.PermutationIndex → Bool) (publicLabels : EncPRF.PermutationIndex → Block)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (miss : bridgeKey ∉ transcriptHashInputs transcript)
    (budget : Nat) (lengthBound : transcript.length ≤ budget)
    (fits : ∀ index, 2 + Fintype.card (EncQueryDomain (encOracleTranscriptRecords transcript) index) ≤
      Fintype.card Block) :
    ((1 - ((4 * budget : Nat) : ℝ≥0∞) / Fintype.card Block) *
      encTranscriptFactor (encOracleTranscriptRecords transcript)) *
      (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
        (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) ×
          (InputMacKey × InputMacKey))).toOuterMeasure
          {coin | (independentKeyLabelsEquiv selected coin.2).1 = publicLabels ∧
            independentFullCircuitSource outputKeys pointRandomness bridgeKey mask.value r1 r2
              coin.2.2 coin.2.1 (circuitSourceQuotients source) coin.1 =
                (lifts, sourceCiphertexts source) ∧
            OracleTranscriptCompatible Garbling.oracleHandler
              {{randomness with hashOracle := hash} with fixedKeyOracle := coin.1} transcript ∧
            EncSourceGood coin.2.1 coin.2.2}) ≤
    (PMF.uniformOfFintype (((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) ×
      ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle))).toOuterMeasure
      (actualLinkedTagKeyEvent outputKeys pointRandomness bridgeKey r1 r2 mask randomness
        source lifts selected publicLabels transcript) := by
  have law := guarded_average_factor
    (fun key => (selectedKeyLabelsEquiv selected key).1 = publicLabels)
    (fun fixed hash => OracleTranscriptCompatible Garbling.oracleHandler
      {randomness with fixedKeyOracle := fixed, hashOracle := hash} transcript)
    EncSourceGood
    (fun fixed key target => independentFullCircuitSource outputKeys pointRandomness bridgeKey mask.value r1 r2
      target key (circuitSourceQuotients source) fixed = (lifts, sourceCiphertexts source))
    ((1 - ((4 * budget : Nat) : ℝ≥0∞) / Fintype.card Block) *
      encTranscriptFactor (encOracleTranscriptRecords transcript))
  have bound := actualLinkedTagKey_mass_ge outputKeys pointRandomness bridgeKey r1 r2 mask
    randomness source lifts selected publicLabels transcript miss budget lengthBound fits
  apply le_trans _ bound
  convert law.symm.le using 1
  · rfl
  apply tsum_congr
  intro coin
  congr 1
  split_ifs with labels
  · apply tsum_congr
    intro hash
    congr 1
    split_ifs with compatible
    · congr 1
      apply tsum_congr
      intro target
      congr 1
      split_ifs <;> rfl
    · rfl
  · rfl

end
end Kriterion.ArgoMAC.Security
