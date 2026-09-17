import Proof.Privacy.Source.Invalid.InvalidAveragedBound
import Proof.Privacy.Source.SourcePrefixReference

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
  instDecidableEqRawCircuitGate_1 fixedQueryDomainFintype transcriptOracleFintype
attribute [local instance] instNonemptyInputMacKey_proof_8

/-- Equal nonfixed functions give equal compatibility conditions. -/
theorem nonfixedReference_congr (first second : Garbling.Randomness)
    (enc : first.encPRFOracle = second.encPRFOracle) (hash : first.hashOracle = second.hashOracle)
    (history : List (Sigma Garbling.oracleSpec.Answer)) :
    NonFixedTranscriptCompatible first history ↔ NonFixedTranscriptCompatible second history := by
  induction history with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨query, answer⟩
    cases query <;> simp only [NonFixedTranscriptCompatible, enc, hash, ih]

/-- Nonfixed compatibility supplies the complete Enc reference. -/
theorem nonfixedReference_enc (randomness : Garbling.Randomness)
    (history : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : NonFixedTranscriptCompatible randomness history) :
    PermutationTranscriptMatches randomness.encPRFOracle (encOracleTranscriptRecords history) := by
  induction history with
  | nil => simp [encOracleTranscriptRecords, PermutationTranscriptMatches]
  | cons entry tail ih =>
    rcases entry with ⟨query, answer⟩
    cases query <;> simp only [NonFixedTranscriptCompatible] at compatible <;>
      simp only [encOracleTranscriptRecords]
    · exact ih compatible
    · exact ih compatible
    · simpa [PermutationTranscriptMatches] using And.intro compatible.1 (ih compatible.2)
    · rename_i index output
      have forward := congrArg (randomness.encPRFOracle.permutation index) compatible.1
      simp only [Equiv.apply_symm_apply] at forward
      simpa [PermutationTranscriptMatches] using And.intro forward.symm (ih compatible.2)
    · exact ih compatible.2

/-- The common prefix state commutes with a nonfixed reference update. -/
theorem sourcePrefixReference_nonfixed (reference : SimulatorState) (rest : GarblingSourceRest)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle) :
    sourcePrefixReference reference {rest with encPRFOracle := enc, hashOracle := hash} =
      {sourcePrefixReference reference rest with encOracle := enc, hashOracle := hash} := rfl

/-- The common references supply a compatible restored prefix. -/
theorem rebasedPrefix_compatible (rest : GarblingSourceRest) (reference : SimulatorState)
    (witness : Garbling.Randomness) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (nonfixed : NonFixedTranscriptCompatible witness (before ++ after)) :
    OracleTranscriptCompatible idealOracleHandler
      (sourcePrefixReference reference {rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle}) before := by
  apply sourcePrefixReference_compatible reference _ before compatible
  apply (nonfixedReference_congr ({rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle} : GarblingSourceRest).reference witness rfl rfl before).mpr
  exact ((nonFixedTranscriptCompatible_append witness before after).mp nonfixed).1

set_option maxRecDepth 4096 in
/-- The invalid count uses the common complete nonfixed reference. -/
def invalidRebasedReference_mass_ge [fieldCert : FieldCertificate] [groupCert : GroupCertificate]
    [blockFinite : Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (witness : Garbling.Randomness)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (lifts : RawCircuitGate → FullHashLift) (tables : CircuitMaskTables)
    (invalid : ¬ OnCurve input)
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (nonfixed : NonFixedTranscriptCompatible witness (before ++ after))
    (miss : rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after))
    (budget : Nat) (small : budget < 2 ^ 100) (bounded : (before ++ after).length ≤ budget) :=
  @invalidTagGoodEvent_average_mass_ge fieldCert groupCert blockFinite
    {rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle} outputKeys table input key
    (sourcePrefixReference reference {rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle}) before after lifts tables
    invalid rfl rfl rfl
    (rebasedPrefix_compatible rest reference witness before after compatible nonfixed)
    miss (nonfixedReference_enc witness (before ++ after) nonfixed)
    budget small bounded
    (sourcePrefixReference_oracleExists reference {rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle} before compatible)

/-- The resampled invalid event removes the common nonfixed reference update. -/
theorem invalidRebasedEvent_eq [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (witness : Garbling.Randomness)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (tag : FullCircuitSource)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle) :
    invalidTagGoodEvent
      {{rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle} with encPRFOracle := enc, hashOracle := hash}
      outputKeys table input key
      {sourcePrefixReference reference {rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle}
        with encOracle := enc, hashOracle := hash} before after tag =
    invalidTagGoodEvent {rest with encPRFOracle := enc, hashOracle := hash}
      outputKeys table input key {sourcePrefixReference reference rest with encOracle := enc, hashOracle := hash}
      before after tag := rfl

/-- The complete linked tag upper mass removes the common nonfixed reference update. -/
theorem invalidRebasedUpper_eq [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (witness : Garbling.Randomness) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (lifts : RawCircuitGate → FullHashLift) (tables : CircuitMaskTables) :
    (if FullSourceComplete (lifts, tables).1 ∧
      retainedFullTable {rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle} outputKeys (lifts, tables) = table
      then (fullSourceTagDensity (lifts, tables))⁻¹ *
        retainedLinkedTagMass {rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle}
          outputKeys (lifts, tables) input (key.encodeAffine input) (before ++ after) else 0) =
    if FullSourceComplete (lifts, tables).1 ∧ retainedFullTable rest outputKeys (lifts, tables) = table
      then (fullSourceTagDensity (lifts, tables))⁻¹ *
        retainedLinkedTagMass rest outputKeys (lifts, tables) input (key.encodeAffine input) (before ++ after) else 0 := by
  rw [retainedFullTable_nonfixed, retainedLinkedTagMass_nonfixed]

private theorem averaged_event_bound {First Second Sample : Type*}
    (first : PMF First) (second : PMF Second) (samples : PMF Sample)
    (left right : First → Second → Set Sample) (factor upper : ℝ≥0∞)
    (bound : factor * (∑' a, first a * ∑' b, second b * samples.toOuterMeasure (left a b)) ≤ upper)
    (same : ∀ a b, left a b = right a b) :
    factor * (∑' a, first a * ∑' b, second b * samples.toOuterMeasure (right a b)) ≤ upper := by
  have equal : left = right := funext fun a => funext fun b => same a b
  subst right
  exact bound

set_option maxRecDepth 4096 in
private theorem invalidRestRebasedFor [fieldCert : FieldCertificate] [groupCert : GroupCertificate]
    [blockFinite : Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (witness : Garbling.Randomness)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (lifts : RawCircuitGate → FullHashLift) (tables : CircuitMaskTables)
    (invalid : ¬ OnCurve input)
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (nonfixed : NonFixedTranscriptCompatible witness (before ++ after))
    (miss : rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after))
    (budget : Nat) (small : budget < 2 ^ 100) (bounded : (before ++ after).length ≤ budget)
    (hashSamples : PMF EncPRF.HashOracle)
    (encSamples : PMF (PermutationOracle EncPRF.PermutationIndex Block))
    (keySamples : PMF ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey))
    (hashEq : hashSamples = PMF.uniformOfFintype EncPRF.HashOracle)
    (encEq : encSamples = PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block))
    (keyEq : keySamples = PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)) :
    (1 - ((186 * budget + 508 : Nat) : ℝ≥0∞) / Fintype.card Block) *
      (∑' hash, hashSamples hash * ∑' enc, encSamples enc * keySamples.toOuterMeasure
        (invalidTagGoodEvent (GarblingSourceRest.mk ({rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle} : GarblingSourceRest).algebraic (@GarblingSourceRest.offsetsClamped ({rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle} : GarblingSourceRest)) enc hash) outputKeys table input key (SimulatorState.mk (sourcePrefixReference reference ({rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle} : GarblingSourceRest)).fixedOracle enc hash (sourcePrefixReference reference ({rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle} : GarblingSourceRest)).fixedTranscript (sourcePrefixReference reference ({rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle} : GarblingSourceRest)).encTranscript (sourcePrefixReference reference ({rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle} : GarblingSourceRest)).hashTranscript (sourcePrefixReference reference ({rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle} : GarblingSourceRest)).commitments (sourcePrefixReference reference ({rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle} : GarblingSourceRest)).linking (sourcePrefixReference reference ({rest with encPRFOracle := witness.encPRFOracle, hashOracle := witness.hashOracle} : GarblingSourceRest)).bad) before after (lifts, tables))) ≤
    if FullSourceComplete (lifts, tables).1 ∧ retainedFullTable rest outputKeys (lifts, tables) = table
      then (fullSourceTagDensity (lifts, tables))⁻¹ *
        retainedLinkedTagMass rest outputKeys (lifts, tables) input (key.encodeAffine input) (before ++ after) else 0 := by
  subst hashSamples
  subst encSamples
  subst keySamples
  have bound := invalidRebasedReference_mass_ge rest outputKeys table input key reference witness before after
    lifts tables invalid compatible nonfixed miss budget small bounded
  have upper := bound.trans_eq (invalidRebasedUpper_eq rest outputKeys table input key witness before after lifts tables)
  exact upper

set_option maxRecDepth 4096 in
/-- The explicit source PMFs keep the per-rest bound usable inside the full source sum. -/
def invalidRestRebased_mass_ge_for [fieldCert : FieldCertificate] [groupCert : GroupCertificate]
    [blockFinite : Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (witness : Garbling.Randomness)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (lifts : RawCircuitGate → FullHashLift) (tables : CircuitMaskTables)
    (invalid : ¬ OnCurve input)
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (nonfixed : NonFixedTranscriptCompatible witness (before ++ after))
    (miss : rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after))
    (budget : Nat) (small : budget < 2 ^ 100) (bounded : (before ++ after).length ≤ budget)
    (hashSamples : PMF EncPRF.HashOracle)
    (encSamples : PMF (PermutationOracle EncPRF.PermutationIndex Block))
    (keySamples : PMF ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey))
    (hashEq : hashSamples = PMF.uniformOfFintype EncPRF.HashOracle)
    (encEq : encSamples = PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block))
    (keyEq : keySamples = PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)) :=
  let bound := invalidRestRebasedFor rest outputKeys table input key reference witness before after lifts tables
    invalid compatible nonfixed miss budget small bounded hashSamples encSamples keySamples hashEq encEq keyEq
  averaged_event_bound hashSamples encSamples keySamples _ _ _ _ bound
    (fun hash enc => invalidRebasedEvent_eq rest outputKeys table input key reference witness before after (lifts, tables) enc hash)

/-- The actual per-rest invalid average uses one common nonfixed witness. -/
def invalidRestRebased_mass_ge [fieldCert : FieldCertificate] [groupCert : GroupCertificate]
    [blockFinite : Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (witness : Garbling.Randomness)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (lifts : RawCircuitGate → FullHashLift) (tables : CircuitMaskTables)
    (invalid : ¬ OnCurve input)
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (nonfixed : NonFixedTranscriptCompatible witness (before ++ after))
    (miss : rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after))
    (budget : Nat) (small : budget < 2 ^ 100) (bounded : (before ++ after).length ≤ budget)
 :=
  invalidRestRebased_mass_ge_for rest outputKeys table input key reference witness before after lifts tables
    invalid compatible nonfixed miss budget small bounded
    (PMF.uniformOfFintype EncPRF.HashOracle)
    (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block))
    (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)) rfl rfl rfl

end
end Kriterion.ArgoMAC.Security
