import Proof.Privacy.Programming.SharedScheduleFreshness
import Proof.Privacy.Collision.SharedPrequeryBound

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 2048
attribute [local irreducible] pipelineGateSchedule scheduleCommands Shared.Simulator.commandRecords

/-- The actual shared schedule is fresh when its row and prequery flags are false. -/
theorem sharedReconstructedCircuitSource_schedule_fresh
    (state : Shared.Simulator.OracleState) (oracle : SimulatorOracleCoin) (bridgeKey mask : BaseField)
    (sample : PublicSample) (rows : FieldMacToECMac.Rows) (input : AffineInput)
    (curveTarget : BaseField)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (key : InputMacKey)
    (pointGood : ¬ pointBranchCollision
      (fun row => (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).1)
      (fun row => rows.get row) input targets
      (fun row => (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).2))
    (prefixGood :
      let source := reconstructedCircuitSource sample mask (fun row => rows.get row) input curveTarget targets
      ¬ sharedPrequeryLabelCollision state.fixedTranscript
        (sharedSourcePrequeryUses oracle bridgeKey source
          (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)) state.fixedTranscript) key) :
    let source := reconstructedCircuitSource sample mask (fun row => rows.get row) input curveTarget targets
    let pointKey := EncPRF.transformKey oracle.encOracle (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key
    let garbled := circuitMaskSampleGarble bridgeKey mask rows input source
    FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords (scheduleCommands
      (pipelineGateSchedule garbled.curveRequest garbled.pointRequests input
        (key.encodeAffine input) (pointKey.encodeAffine input)))) := by
  dsimp only
  let source := reconstructedCircuitSource sample mask (fun row => rows.get row) input curveTarget targets
  let pointKey := EncPRF.transformKey oracle.encOracle (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key
  let garbled := circuitMaskSampleGarble bridgeKey mask rows input source
  apply sharedPipelineGateRecords_fresh state.fixedTranscript garbled.curveRequest garbled.pointRequests
    input (key.encodeAffine input) (pointKey.encodeAffine input)
  · apply pipelineGateProgramRecords_pairwise _ _ input (key.encodeAffine input) (pointKey.encodeAffine input)
      (circuitGateKey pointKey key) (circuitSourceSlope source)
      (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)) (circuitSourceTable source)
    · exact fun gate slot active => circuitMaskDirective_record_eq_raw bridgeKey mask rows input source key pointKey gate slot active
    · exact reconstructedCircuitSource_rawOffset_injective sample mask (fun row => rows.get row)
        input curveTarget targets pointGood pointKey key
  · intro directive member slot active
    obtain ⟨gate, rfl⟩ := (mem_pipelineGateSchedule_iff _ _ _ _ _ directive).mp member
    rw [circuitMaskDirective_record_eq_raw bridgeKey mask rows input source key pointKey gate slot active]
    exact sharedSourcePrequeryCollision_false_fresh oracle bridgeKey source
      (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)) state.fixedTranscript
      key prefixGood gate slot

end
end Kriterion.ArgoMAC.Security
