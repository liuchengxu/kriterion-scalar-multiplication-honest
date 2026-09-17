import Proof.Privacy.Source.Invalid.InvalidNonfixedRatio
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  instFintypeEncQueryDomainOfBlock bitAdaptorTableFintype instFintypeCircuitMaskTables
  instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
  fixedQueryDomainFintype transcriptOracleFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
private theorem uniform_mass_nonempty {Sample : Type*} [Fintype Sample]
    (first second : Nonempty Sample) (event : Set Sample) :
    (@PMF.uniformOfFintype Sample _ first).toOuterMeasure event =
      (@PMF.uniformOfFintype Sample _ second).toOuterMeasure event := by
  cases Subsingleton.elim first second
  rfl
private theorem sourceMass_eq [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (lifts : RawCircuitGate → FullHashLift) (tables : CircuitMaskTables)
    (input : AffineInput) (key : InputMacKey) (history : List (Sigma Garbling.oracleSpec.Answer))
    (nonempty : Nonempty (((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) ×
      ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle))) :
    (@PMF.uniformOfFintype (((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) ×
      ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle)) _ nonempty).toOuterMeasure
      (actualLinkedTagKeyEvent outputKeys rest.algebraic.point.pointRandomness
        rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
        rest.algebraic.field.curveMask rest.reference
        (decodeFullSource (lifts, sharedCircuitHashRest rest.reference tables)) lifts
        (inputSelectedLabelBit input) (inputMacCoordinateEquiv (key.encodeAffine input)) history) =
    retainedLinkedTagMass rest outputKeys (lifts, tables) input (key.encodeAffine input) history := by
  have source : decodeFullSource (lifts, sharedCircuitHashRest rest.reference tables) =
      retainedFullSource rest (lifts, tables) := rfl
  have eventEq := congrArg (fun source => actualLinkedTagKeyEvent outputKeys rest.algebraic.point.pointRandomness
    rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
    rest.algebraic.field.curveMask rest.reference source lifts
    (inputSelectedLabelBit input) (inputMacCoordinateEquiv (key.encodeAffine input)) history) source
  have moved := congrArg
    (@PMF.uniformOfFintype (((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) ×
      ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle)) _ nonempty).toOuterMeasure eventEq
  unfold retainedLinkedTagMass
  dsimp only
  exact moved.trans (uniform_mass_nonempty nonempty _
    (actualLinkedTagKeyEvent outputKeys rest.algebraic.point.pointRandomness
      rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
      rest.algebraic.field.curveMask rest.reference (retainedFullSource rest (lifts, tables)) lifts
      (inputSelectedLabelBit input) (inputMacCoordinateEquiv (key.encodeAffine input)) history))

private theorem sourceUpper [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (lifts : RawCircuitGate → FullHashLift) (tables : CircuitMaskTables)
    (input : AffineInput) (key : InputMacKey) (history : List (Sigma Garbling.oracleSpec.Answer))
    {nonempty : Nonempty (((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) ×
      ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle))} :
    (fullSourceTagDensity (lifts, sourceCiphertexts (decodeFullSource
      (lifts, sharedCircuitHashRest rest.reference tables))))⁻¹ *
    (@PMF.uniformOfFintype (((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) ×
      ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle)) _ nonempty).toOuterMeasure
      (actualLinkedTagKeyEvent outputKeys rest.algebraic.point.pointRandomness
        rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
        rest.algebraic.field.curveMask rest.reference
        (decodeFullSource (lifts, sharedCircuitHashRest rest.reference tables)) lifts
        (inputSelectedLabelBit input) (inputMacCoordinateEquiv (key.encodeAffine input)) history) =
    (fullSourceTagDensity (lifts, tables))⁻¹ *
      retainedLinkedTagMass rest outputKeys (lifts, tables) input (key.encodeAffine input) history := by
  have densityEq :
      (fullSourceTagDensity (lifts, sourceCiphertexts
        (decodeFullSource (lifts, sharedCircuitHashRest rest.reference tables))))⁻¹ =
      (fullSourceTagDensity (lifts, tables))⁻¹ :=
    congrArg (fun tables => (fullSourceTagDensity (lifts, tables))⁻¹)
      (retainedFullSource_ciphertexts rest (lifts, tables))
  have massEq := sourceMass_eq rest outputKeys lifts tables input key history nonempty
  exact congrArg₂ (HMul.hMul : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) densityEq massEq

set_option maxRecDepth 4096 in
/-- The actual retained source satisfies the averaged curve-only relative bound. -/
def retainedInvalidProgrammed_mass_ge [FieldCertificate] [GroupCertificate]
    [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (lifts : RawCircuitGate → FullHashLift) (tables : CircuitMaskTables)
    (state : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (complete : FullSourceComplete lifts)
    (good : ¬ rawSourceBad (validSourceCoin rest key) (retainedFullSource rest (lifts, tables)) input before)
    (members : ∀ record, record ∈ state.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords before)
    (miss : rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after))
    (reference : PermutationTranscriptMatches rest.encPRFOracle (encOracleTranscriptRecords (before ++ after)))
    (budget : Nat) (small : budget < 2 ^ 100) (bounded : (before ++ after).length ≤ budget)
    [Nonempty (TranscriptOracle state.fixedTranscript)] :=
  let bound := fullSourceGood_curve_nonfixed_combined_mass_ge (validSourceCoin rest key) key
    rest.algebraic.field.bridgeKey rfl rfl
    rest.algebraic.field.curveMask (FieldMacToECMac.rowsForOutputKeys outputKeys rest.algebraic.point.pointRandomness)
    (lifts, sharedCircuitHashRest rest.reference tables) lifts rfl input state before after rest.reference
    outputKeys rest.algebraic.point.pointRandomness rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
    (retainedFullSource_randomizers rest (lifts, tables)) (retainedFullSource_residues rest (lifts, tables) complete)
    complete good members miss reference budget small bounded
  bound.trans_eq (sourceUpper rest outputKeys lifts tables input key (before ++ after))

end
end Kriterion.ArgoMAC.Security
