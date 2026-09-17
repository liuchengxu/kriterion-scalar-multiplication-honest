import Proof.Privacy.Source.FullGateCurveTransport
import Proof.Privacy.Source.CurveTransportGood

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

/-- The reconstructed prefix uses the exact complete-source bad event. -/
theorem fullGatePrefixBad_reconstructed [FieldCertificate] [GroupCertificate] {State : Type}
    (retained : MaskRetainedTape)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) :
    fullGatePrefixBad ((fullSourceTape retained full).1, (fullSourceTape retained full).2, selected) ↔
      ¬ FullSourceComplete full.1 ∨
        rawSourceBad (simulatorSourceEquiv (retained.2.2, defaultSimulatorCoin.tableSample)).1
          (decodeFullSource full) selected.1 selected.2.2.2 := by
  have source := fullSourceTape_source retained full
  have hash := congrArg Prod.fst source
  have rest := congrArg Prod.snd source
  dsimp only at hash rest
  simp only [fullGatePrefixBad, fullSourceTape_retained, hash, rest]

/-- The reconstructed ghost result uses the retained bridge key and curve mask. -/
theorem fullGateGhostResult_reconstructed [FieldCertificate] [GroupCertificate] {State : Type}
    (retained : MaskRetainedTape)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) :
    fullGateGhostResult ((fullSourceTape retained full).1, (fullSourceTape retained full).2, selected) =
      retained.2.2.1.1 + retained.2.2.1.2.value * (selected.1.x ^ 3 + 3 - selected.1.y ^ 2) := by
  have keys := congrArg (fun tape : MaskRetainedTape => tape.2.2.1)
    (fullSourceTape_retained retained full)
  change ((fullSourceTape retained full).1.bridgeKey,
    (fullSourceTape retained full).1.curveMask) = retained.2.2.1 at keys
  exact congrArg (fun pair : BaseField × NonZeroBase =>
    pair.1 + pair.2.value * (selected.1.x ^ 3 + 3 - selected.1.y ^ 2)) keys

/-- The reconstructed ghost bad event retains the complete observed transcript. -/
theorem fullGateGhostBad_reconstructed [FieldCertificate] [GroupCertificate] [Fintype BaseField]
    {State : Type} (retained : MaskRetainedTape)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (transcript : FullGateTranscript State) (hidden : BaseField) :
    fullGateGhostBad
      ((((fullSourceTape retained full).1, (fullSourceTape retained full).2, selected), transcript), hidden) ↔
      (¬ FullSourceComplete full.1 ∨
        rawSourceBad (simulatorSourceEquiv (retained.2.2, defaultSimulatorCoin.tableSample)).1
          (decodeFullSource full) selected.1 selected.2.2.2) ∨
      HiddenLinkBad
        (retained.2.2.1.1 + retained.2.2.1.2.value * (selected.1.x ^ 3 + 3 - selected.1.y ^ 2))
        (transcript.2.2.1 ++ transcript.2.2.2.2.2) hidden := by
  simp only [fullGateGhostBad]; rw [fullGatePrefixBad_reconstructed retained full selected, fullGateGhostResult_reconstructed retained full selected]

/-- A complete invalid good prefix remains good after the exact curve change. -/
theorem fullGatePrefixGood_curveTransport [FieldCertificate] [GroupCertificate] {State : Type}
    (retained : MaskRetainedTape)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (key : BaseField) (mask : NonZeroBase) (rows : FieldMacToECMac.Rows)
    (invalid : ¬ OnCurve selected.1)
    (resultEq : retained.2.2.1.1 + retained.2.2.1.2.value *
        (selected.1.x ^ 3 + 3 - selected.1.y ^ 2) =
      key + mask.value * (selected.1.x ^ 3 + 3 - selected.1.y ^ 2))
    (good : ¬ fullGatePrefixBad
      ((fullSourceTape retained full).1, (fullSourceTape retained full).2, selected)) :
    let changed := fullCurveMaskEquiv retained.2.2.1.2.value mask.value selected.1 full
    ¬ fullGatePrefixBad
      ((fullSourceTape (retainedKeyMask retained key mask) changed).1,
        (fullSourceTape (retainedKeyMask retained key mask) changed).2, selected) := by
  classical
  rw [fullGatePrefixBad_reconstructed] at good
  obtain ⟨complete, rawGood⟩ := not_or.mp good
  have complete := not_not.mp complete
  dsimp only
  rw [fullGatePrefixBad_reconstructed]
  apply not_or.mpr
  constructor
  · exact not_not.mpr
      ((fullCurveMaskEquiv_complete_iff retained.2.2.1.2.value mask.value selected.1 full).mpr complete)
  · exact fullCurveMask_good_invalid
      (simulatorSourceEquiv (retained.2.2, defaultSimulatorCoin.tableSample)).1
      retained.2.2.1.2.value key mask.value rows selected.1 full selected.2.2.2
      complete invalid resultEq rawGood

end

end Kriterion.ArgoMAC.Security
