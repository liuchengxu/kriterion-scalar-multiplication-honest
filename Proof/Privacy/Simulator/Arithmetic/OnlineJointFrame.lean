import Proof.Privacy.Simulator.Arithmetic.OnlineJoint
import Proof.Privacy.Simulator.Arithmetic.OnlineTargetBuffers

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorSampling

/-- The selected curve always targets the sampled bridge key. -/
theorem sharedOfflineFrame_curve (coin : OfflineCoin) (input : AffineInput) :
    (sharedOfflineFrame coin).selectedCurve input = coin.1.curve.request.retarget input coin.2.2 := rfl

/-- The bridge key equals the selected curve result for every input. -/
theorem sharedOfflineFrame_curveResult (coin : OfflineCoin) (input : AffineInput) :
    ((sharedOfflineFrame coin).selectedCurve input).result input = coin.2.2 := by
  rw [sharedOfflineFrame_curve, CurveGateRequest.retarget_result]

/-- The original selected labels depend only on the sampled input key and selected input. -/
theorem sharedOfflineFrame_inputMac (coin : OfflineCoin) (input : AffineInput) :
    ((sharedOfflineFrame coin).labels input).inputMac = coin.2.1.encodeAffine input := rfl

/-- Each selected point row uses the three fields written by the target machine. -/
theorem sharedOfflineFrame_pointRow [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (input : AffineInput) (output : Point)
    (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)) (row : Fin FieldMacToECMac.outputMacCount) :
    ((sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2).get row =
      ⟨(coin.1.points.get row).x.request.retarget input (onlineTargetField output sample row 0),
        (coin.1.points.get row).y.request.retarget input (onlineTargetField output sample row 1),
        (coin.1.points.get row).z.request.retarget input (onlineTargetField output sample row 2)⟩ := by
  simp only [CircuitSimulatorState.selectedPoints, retargetPointGateRequests_get,
    sharedOfflineFrame, Shared.Simulator.initialState, PublicSample.pointRequests, Vector.get_map,
    RowPublicSample.request, BiquadraticRowRequest.retarget, onlineTargetField]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
