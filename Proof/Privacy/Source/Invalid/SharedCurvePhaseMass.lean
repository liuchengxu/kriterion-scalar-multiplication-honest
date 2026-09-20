import Proof.Privacy.Source.Invalid.SharedCurveSourceEvent
import Proof.Privacy.Source.SharedGateSourceEndpointMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- This weight keeps the complete shared curve source guard at the observed transcript. -/
def sharedCurveSourcePhaseWeight [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) (tag : FullCircuitSource)
    (output : SharedFullGateTranscript adversary.State) : ENNReal :=
  let data : GarblingOracleData := ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩
  if SharedCurveTagGood rest keys output.1 output.2.1.1 sample.2
      (transcriptFinalState idealOracleHandler (sharedInitialSourceOracle data) output.2.2.1)
      (output.2.2.1 ++ output.2.2.2.2.2) tag then
    ((sharedGateSourceChoose adversary parameter auxiliary (retainedFullTable rest keys tag) data).bind fun choice =>
      sharedGateSourceObserve adversary parameter auxiliary (retainedFullTable rest keys tag) choice
        (selectedGateView (circuitMaskSampleGarble rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask.value
          (FieldMacToECMac.rowsForOutputKeys keys rest.algebraic.point.pointRandomness)
          choice.1 (retainedFullSource rest tag)) choice.1) data) output
  else 0

private theorem guard_factor (phase : ENNReal) (guard table first labels last : Prop)
    [Decidable guard] [Decidable table] [Decidable first] [Decidable labels] [Decidable last]
    (tableOfGuard : guard → table) :
    (if guard then phase * (if table ∧ first ∧ labels ∧ last then 1 else 0) else 0) =
      phase * (if labels ∧ guard ∧ first ∧ last then 1 else 0) := by
  by_cases good : guard
  · simp only [good, if_true, tableOfGuard good, true_and, and_true]
    by_cases a : first <;> by_cases b : labels <;> by_cases c : last <;> simp [a, b, c]
  · simp only [good, if_false, and_false, false_and, mul_zero]

/-- The guarded shared curve source has the exact two-phase event mass. -/
theorem sharedCurveSourcePhaseWeight_event [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) (tag : FullCircuitSource)
    (table : Pipeline.Table) (referenceBefore referenceAfter : Shared.Simulator.OracleState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (key : InputMacKey)
    (invalid : ¬ OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    sharedCurveSourcePhaseWeight adversary parameter auxiliary rest keys sample tag
      (table, selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter table auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
    (if sample ∈ sharedCurveTagEvent rest keys table selected.1 key
      (sharedSourcePrefixReference referenceBefore rest) before after tag then 1 else 0) := by
  unfold sharedCurveSourcePhaseWeight
  dsimp only
  rw [sharedGateSourcePhases_mass_factor_at adversary parameter auxiliary
    (retainedFullTable rest keys tag) table
    ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩
    (fun input => selectedGateView (circuitMaskSampleGarble rest.algebraic.field.bridgeKey
      rest.algebraic.field.curveMask.value
      (FieldMacToECMac.rowsForOutputKeys keys rest.algebraic.point.pointRandomness)
      input (retainedFullSource rest tag)) input)
    referenceBefore referenceAfter selected labels decision before after firstCompatible secondCompatible]
  rw [guard_factor _ _ _ _ _ _ (fun good => good.2.1)]
  have event := sharedCurveTagEvent_iff_source rest keys table selected.1 key referenceBefore before after
    firstCompatible tag labels invalid bits mac sample
  dsimp only at event
  rw [event]
  simp only [sourceInputLabels]
  congr 1
  exact (ite_eq_ite _ _ _).mpr trivial

end
end Kriterion.ArgoMAC.Security
