import Proof.Privacy.Source.Invalid.SharedCurveEventRatio
import Proof.Privacy.Source.Invalid.InvalidSourceTransport

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
attribute [local instance 10] Classical.propDecidable
attribute [local instance] circuitMaskSampleFintype bitAdaptorTableFintype
  instNonemptyPublicSample_2
local instance sharedInvalidRemainderNonempty {count : Nat} : Nonempty (BiquadraticSampleRemainder count) :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable,
    fun _ _ => defaultHashLiftQuotient)⟩
set_option maxRecDepth 2048
attribute [local irreducible] Shared.Simulator.commands scheduleCommands circuitMaskSampleGarble

/-- This observer runs the actual shared curve commands after the selected input. -/
def sharedInvalidCurveObserve [FieldCertificate] {Aux Observation : Type*}
    (key : InputMacKey) (state : Aux → Shared.Simulator.OracleState)
    (observe : Pipeline.Table → (AffineInput × Aux) → BaseField → Shared.Simulator.OracleState → PMF Observation)
    (table : Pipeline.Table) (selected : AffineInput × Aux) (bridge : BaseField)
    (request : CurveGateRequest) : PMF (Option Observation) :=
  if OnCurve selected.1 then PMF.pure none else
    (observe table selected bridge (Shared.Simulator.commands (state selected.2)
      (scheduleCommands (request.schedule selected.1 (key.encodeAffine selected.1))))).map some

/-- This source runs the actual masked curve request with the shared oracle held fixed. -/
def sharedInvalidCurveMaskRun [FieldCertificate] {Aux Observation : Type*}
    (bridge mask : BaseField) (rows : FieldMacToECMac.Rows) (key : InputMacKey)
    (state : Aux → Shared.Simulator.OracleState)
    (choose : Pipeline.Table → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → BaseField → Shared.Simulator.OracleState → PMF Observation) :
    PMF (Option Observation) :=
  (PMF.uniformOfFintype CircuitMaskSample).bind fun source =>
    let table := circuitMaskSourceTable bridge mask rows source
    (choose table).bind fun selected =>
      sharedInvalidCurveObserve key state observe table selected bridge
        (circuitMaskSampleGarble bridge mask rows selected.1 source).curveRequest

/-- The full adaptive source split preserves the actual shared curve commands. -/
theorem sharedInvalidCurveMaskRun_retarget [FieldCertificate] {Aux Observation : Type*}
    (bridge mask : BaseField) (rows : FieldMacToECMac.Rows)
    (sparse : ∀ row, FieldMacToECMac.SparseRow (rows.get row)) (key : InputMacKey)
    (state : Aux → Shared.Simulator.OracleState)
    (choose : Pipeline.Table → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → BaseField → Shared.Simulator.OracleState → PMF Observation) :
    sharedInvalidCurveMaskRun bridge mask rows key state choose observe =
      (PMF.uniformOfFintype PublicSample).bind fun sample =>
        (choose (publicMaskTable sample)).bind fun selected =>
          sharedInvalidCurveObserve key state observe (publicMaskTable sample) selected bridge
            (sample.curveRequest.retarget selected.1 (bridge + mask * (selected.1.x ^ 3 + 3 - selected.1.y ^ 2))) := by
  have law := congrArg (fun distribution => distribution.bind
    (fun pair : (AffineInput × Aux) × PublicSample =>
      sharedInvalidCurveObserve key state observe (publicMaskTable pair.2) pair.1 bridge pair.2.curveRequest))
    (adaptiveCircuitMaskGarble_eq_retarget bridge mask rows sparse choose)
  have table (input : AffineInput) (source : CircuitMaskSample) :
      publicMaskTable (circuitMaskSampleGarble bridge mask rows input source) =
        circuitMaskSourceTable bridge mask rows source :=
    circuitMaskSampleGarble_table_input bridge mask rows source input ⟨0, 0⟩
  simp only [PMF.bind_bind, PMF.bind_map] at law
  dsimp only [Function.comp_def] at law
  simp only [table, publicMaskTable_retarget, PublicSample.retargetMask_curveRequest] at law
  exact law

/-- This selected source holds the shared oracle and all earlier answers fixed. -/
def sharedInvalidCurveChoice {Aux : Type*} (choose : Pipeline.Table → PMF (AffineInput × Aux)) :
    PMF (AffineInput × (PublicSample × Aux)) :=
  (PMF.uniformOfFintype PublicSample).bind fun sample =>
    (choose (publicMaskTable sample)).map fun selected => (selected.1, sample, selected.2)

/-- A full field mask gives the independent invalid curve result under the actual shared interpreter. -/
theorem sharedInvalidCurveMask_full_eq [FieldCertificate] {Aux Observation : Type*}
    (key : InputMacKey) (state : Aux → Shared.Simulator.OracleState)
    (choose : Pipeline.Table → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → BaseField → Shared.Simulator.OracleState → PMF Observation) :
    ((sharedInvalidCurveChoice choose).bind fun selected =>
      (PMF.uniformOfFintype (BaseField × BaseField)).bind fun pair =>
        sharedInvalidCurveObserve key state observe (publicMaskTable selected.2.1)
          (selected.1, selected.2.2) pair.1
          (selected.2.1.curveRequest.retarget selected.1
            (pair.1 + pair.2 * (selected.1.x ^ 3 + 3 - selected.1.y ^ 2)))) =
    ((sharedInvalidCurveChoice choose).bind fun selected =>
      (PMF.uniformOfFintype (BaseField × BaseField)).bind fun pair =>
        sharedInvalidCurveObserve key state observe (publicMaskTable selected.2.1)
          (selected.1, selected.2.2) pair.1 (selected.2.1.curveRequest.retarget selected.1 pair.2)) := by
  have law := adaptiveCurveKey_uniform (sharedInvalidCurveChoice choose)
    (fun selected bridge result => sharedInvalidCurveObserve key state observe (publicMaskTable selected.2.1)
      (selected.1, selected.2.2) bridge (selected.2.1.curveRequest.retarget selected.1 result))
  apply law.trans
  apply congrArg (sharedInvalidCurveChoice choose).bind
  funext selected
  apply congrArg (PMF.uniformOfFintype (BaseField × BaseField)).bind
  funext pair
  by_cases valid : OnCurve selected.1
  · simp only [sharedInvalidCurveObserve, if_pos valid]
  · simp only [selectedCurveIdealResult, if_neg valid]

/-- The independent curve-mask coins commute with the actual shared adaptive input choice. -/
theorem sharedInvalidCurveMaskRun_average_eq [FieldCertificate] {Aux Observation : Type*}
    (rows : FieldMacToECMac.Rows) (sparse : ∀ row, FieldMacToECMac.SparseRow (rows.get row))
    (key : InputMacKey) (state : Aux → Shared.Simulator.OracleState)
    (choose : Pipeline.Table → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → BaseField → Shared.Simulator.OracleState → PMF Observation) :
    ((PMF.uniformOfFintype BaseField).bind fun bridge =>
      (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
        sharedInvalidCurveMaskRun bridge mask.value rows key state choose observe) =
      ((sharedInvalidCurveChoice choose).bind fun selected =>
        (PMF.uniformOfFintype BaseField).bind fun bridge =>
          (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
            sharedInvalidCurveObserve key state observe (publicMaskTable selected.2.1)
              (selected.1, selected.2.2) bridge
              (selected.2.1.curveRequest.retarget selected.1
                (bridge + mask.value * (selected.1.x ^ 3 + 3 - selected.1.y ^ 2)))) := by
  simp_rw [sharedInvalidCurveMaskRun_retarget _ _ rows sparse key state choose observe]
  simp_rw [PMF.bind_comm (PMF.uniformOfFintype NonZeroBase) (PMF.uniformOfFintype PublicSample)]
  rw [PMF.bind_comm (PMF.uniformOfFintype BaseField) (PMF.uniformOfFintype PublicSample)]
  simp only [sharedInvalidCurveChoice, PMF.bind_bind, PMF.bind_map]
  apply congrArg (PMF.uniformOfFintype PublicSample).bind
  funext sample
  simp_rw [PMF.bind_comm (PMF.uniformOfFintype NonZeroBase) (choose (publicMaskTable sample))]
  rw [PMF.bind_comm (PMF.uniformOfFintype BaseField) (choose (publicMaskTable sample))]
  rfl

/-- The exact invalid shared interpreter pays one field inverse when the real mask excludes zero. -/
theorem sharedInvalidCurveMask_observation_bound [FieldCertificate] {Aux Observation : Type*}
    (rows : FieldMacToECMac.Rows) (sparse : ∀ row, FieldMacToECMac.SparseRow (rows.get row))
    (key : InputMacKey) (state : Aux → Shared.Simulator.OracleState)
    (choose : Pipeline.Table → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → BaseField → Shared.Simulator.OracleState → PMF Observation)
    (event : Set (Option Observation)) :
    |(((sharedInvalidCurveChoice choose).bind fun selected =>
        (PMF.uniformOfFintype (BaseField × BaseField)).bind fun pair =>
          sharedInvalidCurveObserve key state observe (publicMaskTable selected.2.1)
            (selected.1, selected.2.2) pair.1
            (selected.2.1.curveRequest.retarget selected.1 pair.2)).toOuterMeasure event).toReal -
      (((PMF.uniformOfFintype BaseField).bind fun bridge =>
        (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
          sharedInvalidCurveMaskRun bridge mask.value rows key state choose observe).toOuterMeasure event).toReal| ≤
      1 / (baseFieldModulus : ℝ) := by
  have bound := adaptiveCurveMask_observation_bound (sharedInvalidCurveChoice choose)
    (fun selected bridge result => sharedInvalidCurveObserve key state observe (publicMaskTable selected.2.1)
      (selected.1, selected.2.2) bridge (selected.2.1.curveRequest.retarget selected.1 result)) event
  have ideal (selected : AffineInput × (PublicSample × Aux)) (pair : BaseField × BaseField) :
      sharedInvalidCurveObserve key state observe (publicMaskTable selected.2.1)
        (selected.1, selected.2.2) pair.1
        (selected.2.1.curveRequest.retarget selected.1 (selectedCurveIdealResult selected.1 pair)) =
      sharedInvalidCurveObserve key state observe (publicMaskTable selected.2.1)
        (selected.1, selected.2.2) pair.1 (selected.2.1.curveRequest.retarget selected.1 pair.2) := by
    by_cases valid : OnCurve selected.1
    · simp only [sharedInvalidCurveObserve, if_pos valid]
    · simp only [selectedCurveIdealResult, if_neg valid]
  simp_rw [ideal] at bound
  rw [← sharedInvalidCurveMaskRun_average_eq rows sparse key state choose observe] at bound
  exact bound

end
end Kriterion.ArgoMAC.Security
