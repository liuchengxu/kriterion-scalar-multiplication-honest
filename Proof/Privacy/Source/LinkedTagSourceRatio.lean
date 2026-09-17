import Proof.Privacy.Source.HiddenEncSourceRatio
import Proof.Privacy.Source.RealCircuitSource

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype instFintypeEncQueryDomainOfBlock
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The relative nonfixed-oracle count restores the actual linked full source tag. -/
theorem actualLinkedTagTranscript_mass_ge [Fintype Block] [Fintype BaseField]
    (outputKeys : OutputKeys) (pointRandomness : Randomness)
    (bridgeKey r1 r2 : BaseField) (mask : NonZeroBase) (inputKey : InputMacKey)
    (randomness : Garbling.Randomness) (source : CircuitMaskSample)
    (lifts : RawCircuitGate → FullHashLift)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (miss : bridgeKey ∉ transcriptHashInputs transcript)
    (budget : Nat) (lengthBound : transcript.length ≤ budget)
    (fits : ∀ index, 2 + Fintype.card (EncQueryDomain (encOracleTranscriptRecords transcript) index) ≤
      Fintype.card Block) :
    (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
      if OracleTranscriptCompatible Garbling.oracleHandler {randomness with hashOracle := hash} transcript then
        (1 - ((4 * budget : Nat) : ℝ≥0∞) / Fintype.card Block) *
          encTranscriptFactor (encOracleTranscriptRecords transcript) *
          (∑' target, (PMF.uniformOfFintype InputMacKey) target *
            if EncSourceGood inputKey target then
              (if independentFullCircuitSource outputKeys pointRandomness bridgeKey mask.value r1 r2
                target inputKey (circuitSourceQuotients source) randomness.fixedKeyOracle =
                  (lifts, sourceCiphertexts source) then 1 else 0) else 0) else 0) ≤
    ∑' enc : PermutationOracle EncPRF.PermutationIndex Block,
      (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) enc *
        ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
          if OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with encPRFOracle := enc, hashOracle := hash} transcript then
              (if actualFullCircuitSource outputKeys pointRandomness bridgeKey r1 r2 mask
                randomness.fixedKeyOracle enc hash inputKey = (lifts, sourceCiphertexts source)
                  then 1 else 0) else 0 := by
  have bound := hiddenEncSource_weighted_mass_ge bridgeKey inputKey randomness transcript miss
    budget lengthBound fits (fun target =>
      if independentFullCircuitSource outputKeys pointRandomness bridgeKey mask.value r1 r2
        target inputKey (circuitSourceQuotients source) randomness.fixedKeyOracle =
          (lifts, sourceCiphertexts source) then 1 else 0)
  apply bound.trans_eq
  apply tsum_congr
  intro enc
  apply congrArg (fun mass => (PMF.uniformOfFintype
    (PermutationOracle EncPRF.PermutationIndex Block)) enc * mass)
  apply tsum_congr
  intro hash
  apply congrArg (fun mass => (PMF.uniformOfFintype EncPRF.HashOracle) hash * mass)
  have tagEq := independentFullCircuitSource_linked outputKeys pointRandomness bridgeKey r1 r2 mask
    randomness.fixedKeyOracle enc hash inputKey (circuitSourceQuotients source)
  dsimp only [EncPRF.whiteningKeys] at tagEq
  rw [tagEq]

end
end Kriterion.ArgoMAC.Security
