import Proof.Privacy.Source.Invalid.RetainedInvalidProgrammed
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable transcriptOracleFintype

/-- The retained raw coefficient is the exact curve-only programmed mass. -/
theorem retainedInvalidCoefficient_eq [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (lifts : RawCircuitGate → FullHashLift)
    (tables : CircuitMaskTables) (state : SimulatorState)
    (after : List (Sigma Garbling.oracleSpec.Answer))
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
      (fixedTranscriptFactor state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map fun oracle =>
          programGateSchedule {state with fixedOracle := oracle.1}
            ((circuitMaskSampleGarble rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask.value
              (FieldMacToECMac.rowsForOutputKeys outputKeys rest.algebraic.point.pointRandomness) input
              (decodeFullSource (lifts, sharedCircuitHashRest rest.reference tables))).curveRequest.schedule
                input (key.encodeAffine input))).toOuterMeasure
          {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)}) =
    invalidFixedProgrammedMass rest outputKeys input key (lifts, tables) state after := by
  unfold invalidFixedProgrammedMass
  apply congrArg ((Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ * ·)
  apply congrArg (fixedTranscriptFactor state.fixedTranscript * ·)
  apply congrArg (fun samples : PMF SimulatorState => samples.toOuterMeasure
    {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)})
  apply congrArg (PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
  funext oracle
  rfl
end
end Kriterion.ArgoMAC.Security
