import Proof.Privacy.Source.Invalid.InvalidAverageRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
  instDecidableEqRawCircuitGate_1 fixedQueryDomainFintype transcriptOracleFintype
attribute [local instance] instNonemptyInputMacKey_proof_8

private theorem relative_average_congr {First Second : Type*}
    (first : PMF First) (second : PMF Second) (condition : First → Second → Prop)
    {conditionDec : ∀ a b, Decidable (condition a b)}
    (factor left right result : ℝ≥0∞)
    (bound : factor * (∑' a, first a * ∑' b, second b * @ite ℝ≥0∞ (condition a b) (conditionDec a b) left 0) ≤ result) (equal : left = right) :
    factor * (∑' a, first a * ∑' b, second b * @ite ℝ≥0∞ (condition a b) (conditionDec a b) right 0) ≤ result := by
  subst right
  exact bound

set_option maxRecDepth 4096 in
private theorem retainedInvalidFor [fieldCert : FieldCertificate] [groupCert : GroupCertificate] [blockFinite : Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (lifts : RawCircuitGate → FullHashLift) (tables : CircuitMaskTables)
    (state : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (complete : FullSourceComplete lifts)
    (good : ¬ rawSourceBad (validSourceCoin rest key) (retainedFullSource rest (lifts, tables)) input before)
    (members : ∀ record, record ∈ state.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords before)
    (miss : rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after))
    (reference : PermutationTranscriptMatches rest.encPRFOracle (encOracleTranscriptRecords (before ++ after)))
    (budget : Nat) (small : budget < 2 ^ 100) (bounded : (before ++ after).length ≤ budget)
    [fiberNonempty : Nonempty (TranscriptOracle state.fixedTranscript)]
    (hashSamples : PMF EncPRF.HashOracle)
    (encSamples : PMF (PermutationOracle EncPRF.PermutationIndex Block))
    (hashEq : hashSamples = PMF.uniformOfFintype EncPRF.HashOracle)
    (encEq : encSamples = PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) :
    (1 - ((186 * budget + 508 : Nat) : ℝ≥0∞) / Fintype.card Block) *
      (∑' hash, hashSamples hash * ∑' enc, encSamples enc *
        if NonFixedTranscriptCompatible (nonfixedSourceReference rest.reference enc hash) (before ++ after)
        then ((Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
      (fixedTranscriptFactor state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map fun oracle =>
          programGateSchedule {state with fixedOracle := oracle.1}
            ((circuitMaskSampleGarble rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask.value
              (FieldMacToECMac.rowsForOutputKeys outputKeys rest.algebraic.point.pointRandomness) input
              (decodeFullSource (lifts, sharedCircuitHashRest rest.reference tables))).curveRequest.schedule
                input (key.encodeAffine input))).toOuterMeasure
          {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)})) else 0) ≤
      (fullSourceTagDensity (lifts, tables))⁻¹ *
        retainedLinkedTagMass rest outputKeys (lifts, tables) input (key.encodeAffine input) (before ++ after) := by
  subst hashSamples
  subst encSamples
  exact @retainedInvalidProgrammed_mass_ge fieldCert groupCert blockFinite rest outputKeys input key lifts tables
    state before after complete good members miss reference budget small bounded fiberNonempty

set_option maxRecDepth 4096 in
private def retainedInvalidNamedFor [fieldCert : FieldCertificate] [groupCert : GroupCertificate] [blockFinite : Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (lifts : RawCircuitGate → FullHashLift) (tables : CircuitMaskTables)
    (state : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (complete : FullSourceComplete lifts)
    (good : ¬ rawSourceBad (validSourceCoin rest key) (retainedFullSource rest (lifts, tables)) input before)
    (members : ∀ record, record ∈ state.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords before)
    (miss : rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after))
    (reference : PermutationTranscriptMatches rest.encPRFOracle (encOracleTranscriptRecords (before ++ after)))
    (budget : Nat) (small : budget < 2 ^ 100) (bounded : (before ++ after).length ≤ budget)
    [fiberNonempty : Nonempty (TranscriptOracle state.fixedTranscript)]
    (hashSamples : PMF EncPRF.HashOracle)
    (encSamples : PMF (PermutationOracle EncPRF.PermutationIndex Block))
    (hashEq : hashSamples = PMF.uniformOfFintype EncPRF.HashOracle)
    (encEq : encSamples = PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) :=
  let bound := retainedInvalidFor rest outputKeys input key lifts tables state before after complete good members
    miss reference budget small bounded hashSamples encSamples hashEq encEq
  relative_average_congr hashSamples encSamples
    (fun hash enc => NonFixedTranscriptCompatible (nonfixedSourceReference rest.reference enc hash) (before ++ after))
    _ _ _ _ bound
    (@retainedInvalidCoefficient_eq fieldCert groupCert blockFinite rest outputKeys input key lifts tables state after fiberNonempty)

/-- The retained count uses the exact programmed coefficient. -/
def retainedInvalidNamed_mass_ge [fieldCert : FieldCertificate] [groupCert : GroupCertificate] [blockFinite : Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (lifts : RawCircuitGate → FullHashLift) (tables : CircuitMaskTables)
    (state : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (complete : FullSourceComplete lifts)
    (good : ¬ rawSourceBad (validSourceCoin rest key) (retainedFullSource rest (lifts, tables)) input before)
    (members : ∀ record, record ∈ state.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords before)
    (miss : rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after))
    (reference : PermutationTranscriptMatches rest.encPRFOracle (encOracleTranscriptRecords (before ++ after)))
    (budget : Nat) (small : budget < 2 ^ 100) (bounded : (before ++ after).length ≤ budget)
    [fiberNonempty : Nonempty (TranscriptOracle state.fixedTranscript)]
 :=
  retainedInvalidNamedFor rest outputKeys input key lifts tables state before after complete good members
    miss reference budget small bounded
    (PMF.uniformOfFintype EncPRF.HashOracle)
    (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) rfl rfl

set_option maxRecDepth 4096 in
private def invalidAverageFor [fieldCert : FieldCertificate] [groupCert : GroupCertificate] [blockFinite : Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (lifts : RawCircuitGate → FullHashLift) (tables : CircuitMaskTables)
    (empty : initial.fixedTranscript = [])
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    (miss : rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after))
    (reference : PermutationTranscriptMatches rest.encPRFOracle (encOracleTranscriptRecords (before ++ after)))
    (budget : Nat) (small : budget < 2 ^ 100) (bounded : (before ++ after).length ≤ budget)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)]
    (hashSamples : PMF EncPRF.HashOracle)
    (encSamples : PMF (PermutationOracle EncPRF.PermutationIndex Block))
    (hashEq : hashSamples = PMF.uniformOfFintype EncPRF.HashOracle)
    (encEq : encSamples = PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block))
    {keptDec : Decidable (FullSourceComplete (lifts, tables).1 ∧ retainedFullTable rest outputKeys (lifts, tables) = table ∧ ¬ rawSourceBad (validSourceCoin rest key) (retainedFullSource rest (lifts, tables)) input before)}
    (actual : ℝ≥0∞)
    (average : actual = ∑' hash, hashSamples hash * ∑' enc, encSamples enc *
      if NonFixedTranscriptCompatible (nonfixedSourceReference rest.reference enc hash) (before ++ after)
      then @ite ℝ≥0∞ (FullSourceComplete (lifts, tables).1 ∧ retainedFullTable rest outputKeys (lifts, tables) = table ∧ ¬ rawSourceBad (validSourceCoin rest key) (retainedFullSource rest (lifts, tables)) input before) keptDec (invalidFixedProgrammedMass rest outputKeys input key (lifts, tables) (transcriptFinalState idealOracleHandler initial before) after) 0 else 0) :=
  letI := keptDec
  guardedRelativeAverage_le hashSamples encSamples _ _
    (FullSourceComplete (lifts, tables).1 ∧ retainedFullTable rest outputKeys (lifts, tables) = table)
    _ (1 - ((186 * budget + 508 : Nat) : ℝ≥0∞) / Fintype.card Block) actual
    ((fullSourceTagDensity (lifts, tables))⁻¹ *
      retainedLinkedTagMass rest outputKeys (lifts, tables) input (key.encodeAffine input) (before ++ after))
    average (fun kept => ⟨kept.1, kept.2.1⟩)
    (fun kept => retainedInvalidNamedFor rest outputKeys input key lifts tables
      (transcriptFinalState idealOracleHandler initial before) before after kept.1 kept.2.2
      (invalidReference_historyMembers initial before empty compatible) miss reference budget small bounded
      hashSamples encSamples hashEq encEq)

set_option maxRecDepth 4096 in
/-- The actual invalid event satisfies the relative bound after the nonfixed average. -/
def invalidTagGoodEvent_average_mass_ge [fieldCert : FieldCertificate] [groupCert : GroupCertificate] [blockFinite : Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (lifts : RawCircuitGate → FullHashLift) (tables : CircuitMaskTables)
    (invalid : ¬ OnCurve input) (empty : initial.fixedTranscript = [])
    (initialEnc : initial.encOracle = rest.encPRFOracle) (initialHash : initial.hashOracle = rest.hashOracle)
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    (miss : rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after))
    (reference : PermutationTranscriptMatches rest.encPRFOracle (encOracleTranscriptRecords (before ++ after)))
    (budget : Nat) (small : budget < 2 ^ 100) (bounded : (before ++ after).length ≤ budget)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)]
 :=
  let average := invalidTagGoodEvent_nonfixed_average rest outputKeys table input key initial before after
    (lifts, tables) invalid empty initialEnc initialHash compatible
  invalidAverageFor rest outputKeys table input key initial before after lifts tables empty
    compatible miss reference budget small bounded
    (PMF.uniformOfFintype EncPRF.HashOracle)
    (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) rfl rfl _ average

end
end Kriterion.ArgoMAC.Security
