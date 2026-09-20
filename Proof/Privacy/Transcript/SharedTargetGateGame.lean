import Proof.Privacy.Transcript.SharedIdealGateGame

namespace Kriterion.ArgoMAC.Security
open BN254 FieldMacToECMac Cryptography
noncomputable section
attribute [local instance] Classical.propDecidable instNonemptyPublicSample_2 vectorFintype
  rowRandomnessFintype xRandomnessFintype
  yRandomnessFintype zRandomnessFintype

/-- The target source uses the simulator bridge on both input branches. -/
def sharedTargetGateSourceRun [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField)
    (choose : Pipeline.Table → GarblingOracleData → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView → GarblingOracleData → PMF Observation) :
    PMF Observation :=
  (PMF.uniformOfFintype (SharedMaskRetainedTape × PublicSample)).bind fun source =>
    (choose (publicMaskTable source.2) source.1.val.2.2.2).bind fun selected =>
      (PMF.uniformOfFintype ((Fin 90 → Point) ×
        (Fin FieldMacToECMac.outputMacCount → NonZeroBase))).bind fun online =>
          observe (publicMaskTable source.2) selected
            (source.2.curveRequest.retarget selected.1 source.1.val.2.2.1.1,
              (decodePoint selected.1).map fun point => retargetPointGateRequests source.2.pointRequests
                selected.1 (outputTargets (scalarMultiplication scalar point) (Vector.ofFn online.1) online.2))
            source.1.val.2.2.2

/-- The selected curve shift changes only the retained bridge field. -/
def sharedRetainedCurveShift [FieldCertificate] [GroupCertificate] (input : AffineInput) :
    (SharedMaskRetainedTape × PublicSample) ≃ (SharedMaskRetainedTape × PublicSample) where
  toFun source :=
    (⟨(source.1.val.1, source.1.val.2.1,
      (source.1.val.2.2.1.1 + source.1.val.2.2.1.2.value * (input.x ^ 3 + 3 - input.y ^ 2),
        source.1.val.2.2.1.2), source.1.val.2.2.2), source.1.property⟩, source.2)
  invFun source :=
    (⟨(source.1.val.1, source.1.val.2.1,
      (source.1.val.2.2.1.1 - source.1.val.2.2.1.2.value * (input.x ^ 3 + 3 - input.y ^ 2),
        source.1.val.2.2.1.2), source.1.val.2.2.2), source.1.property⟩, source.2)
  left_inv source := by
    rcases source with ⟨⟨⟨offsets, rhos, ⟨bridge, mask⟩, data⟩, shared⟩, sample⟩
    simp
  right_inv source := by
    rcases source with ⟨⟨⟨offsets, rhos, ⟨bridge, mask⟩, data⟩, shared⟩, sample⟩
    simp

/-- The adaptive shift preserves the shared oracle and every public input-choice field. -/
theorem sharedRetainedCurveShift_run [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (choose : Pipeline.Table → GarblingOracleData → PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → (SharedMaskRetainedTape × PublicSample) → PMF Observation) :
    (PMF.uniformOfFintype (SharedMaskRetainedTape × PublicSample)).bind (fun source =>
      (choose (publicMaskTable source.2) source.1.val.2.2.2).bind fun selected =>
        observe selected (sharedRetainedCurveShift selected.1 source)) =
    (PMF.uniformOfFintype (SharedMaskRetainedTape × PublicSample)).bind (fun source =>
      (choose (publicMaskTable source.2) source.1.val.2.2.2).bind fun selected => observe selected source) :=
  uniform_bind_viewEquiv_observe (fun selected : AffineInput × Aux => sharedRetainedCurveShift selected.1)
    (fun source => (publicMaskTable source.2, source.1.val.2.2.2))
    (fun source => (publicMaskTable source.2, source.1.val.2.2.2))
    (fun _ _ => rfl) (fun view => choose view.1 view.2) observe

/-- The exact shared ideal gate source has the simulator's independent target bridge. -/
theorem actualSharedIdealGateSource_eq_target [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField)
    (choose : Pipeline.Table → GarblingOracleData → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView → GarblingOracleData → PMF Observation) :
    actualSharedIdealGateSourceRun scalar (fun table rest => choose table rest.2)
      (fun table selected view rest => observe table selected view rest.2) =
        sharedTargetGateSourceRun scalar choose observe := by
  rw [actualSharedIdealGateSource_coin]
  have shifted := sharedRetainedCurveShift_run choose
    (fun selected source =>
      (PMF.uniformOfFintype ((Fin 90 → Point) × (Fin outputMacCount → NonZeroBase))).bind fun online =>
        observe (publicMaskTable source.2) selected
          (source.2.curveRequest.retarget selected.1 source.1.val.2.2.1.1,
            (decodePoint selected.1).map fun point => retargetPointGateRequests source.2.pointRequests selected.1
              (outputTargets (scalarMultiplication scalar point) (Vector.ofFn online.1) online.2)) source.1.val.2.2.2)
  unfold sharedTargetGateSourceRun
  apply Eq.trans ?_ shifted
  conv_rhs => rw [uniform_prod_eq_bind, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  conv_rhs => rw [PMF.bind_comm]
  simp only [retargetSourceGateView, sharedRetainedCurveShift, Equiv.coe_fn_mk, Option.map_map, Function.comp_def]

/-- The complete shared target source equals the actual ideal simulator transcript. -/
theorem sharedTargetGateSourceRun_eq_idealTranscript [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    sharedTargetGateSourceRun scalar.value (sharedGateSourceChoose adversary parameter auxiliary)
      (sharedGateSourceObserve adversary parameter auxiliary) =
      idealAdaptiveTranscriptWithState sharedInternalCircuit Garbling.topology
        Shared.Simulator.simulator circuitSimulatorOracleHandler adversary parameter scalar auxiliary := by
  rw [sharedIdealTranscript_oracle]
  have law := congrArg (fun distribution : PMF Shared.Simulator.State =>
    sampledTwoPhaseTranscript idealOracleHandler distribution
      CircuitSimulatorState.table (fun state => state.oracle)
      (fun table => adversary.chooseInput parameter table auxiliary)
      (fun state oracle selected =>
        (PMF.uniformOfFintype ((Fin 90 → Point) ×
          (Fin FieldMacToECMac.outputMacCount → NonZeroBase))).map fun online =>
            (state.labels selected.1,
              sharedProgramSelectedGateView oracle selected.1 (state.labels selected.1).inputMac
                (state.selectedCurve selected.1,
                  (checkedScalarMultiplication scalar.value selected.1).map fun point =>
                    state.selectedPoints selected.1 point (Vector.ofFn online.1) online.2)))
      (fun table selected labels => adversary.decide parameter table labels auxiliary selected.2))
    (sharedRetainedSource_initialState_law parameter (Garbling.topology scalar))
  simpa only [sharedTargetGateSourceRun, sharedGateSourceChoose, sharedGateSourceObserve,
    sampledTwoPhaseTranscript, twoPhaseTranscript, PMF.bind_map, PMF.bind_bind,
    PMF.map_bind, PMF.map_comp, Function.comp_def, sharedSourceInitialState,
    Shared.Simulator.initialState, CircuitSimulatorState.table, CircuitSimulatorState.labels,
    CircuitSimulatorState.selectedCurve, CircuitSimulatorState.selectedPoints,
    publicMaskTable, sharedInitialSourceOracle, sourceInputLabels,
    checkedScalarMultiplication, Option.map_map] using law

end
end Kriterion.ArgoMAC.Security
