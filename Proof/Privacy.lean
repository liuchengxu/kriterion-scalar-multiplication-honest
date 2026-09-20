import Proof.Privacy.Simulator.Arithmetic.CompiledOnlineCoupling
import Proof.Privacy.Simulator.Arithmetic.OnlineConcreteSource
import Proof.Privacy.Simulator.Arithmetic.CompiledNullProtocol
import Proof.Privacy.Simulator.Arithmetic.OnlineValidGateParser
import Proof.Privacy.Simulator.Arithmetic.OnlineLinkSharedSource
import Proof.Privacy.Simulator.Arithmetic.OnlineValidPointMemory
import Proof.Privacy.Simulator.Arithmetic.OnlinePreparedCurveRecord
import Proof.Privacy.Simulator.Arithmetic.CompiledAdaptivePrivacy
import Proof.Privacy.Simulator.Arithmetic.CompiledOnlineReady
import Proof.Privacy.Simulator.Arithmetic.OnlineGateJointMachine
import Proof.Privacy.Simulator.Arithmetic.OnlineGateJointSource
import Proof.Privacy.Simulator.Arithmetic.EncLinkSharedMemory
import Proof.Privacy.Simulator.Arithmetic.EncLinkCompleteFrame
import Proof.Privacy.Simulator.Arithmetic.CompiledChosenProtocol
import Proof.Privacy.Simulator.Arithmetic.CompiledDecisionProtocol
import Proof.Privacy.Simulator.Arithmetic.GateDirectiveSchedule
import Proof.Privacy.Simulator.Arithmetic.GateCodeTyped
import Proof.Privacy.Simulator.Arithmetic.GatePrivateBounds
import Proof.Privacy.Simulator.Arithmetic.EncLinkSharedCutoff
import Proof.Privacy.Simulator.Arithmetic.CompiledProgramPrivate
import Proof.Privacy.Simulator.Arithmetic.CompiledBudget
import Proof.Privacy.Simulator.Arithmetic.CompiledOnlineProtocol
import Proof.Privacy.Simulator.Arithmetic.OnlinePrefixBuffers
import Proof.Privacy.Simulator.Arithmetic.OnlineRetargetBuffers
import Proof.Privacy.Simulator.Arithmetic.SharedFiniteSourcePhases
import Proof.Privacy.Simulator.Arithmetic.SharedGateLoopCommands
import Proof.Privacy.Simulator.Arithmetic.SelectedLabelsKeyProtocol
import Proof.Privacy.Simulator.Arithmetic.SharedOnlineCutoffSource
import Proof.Privacy.Simulator.Arithmetic.GateLoopReadySource
import Proof.Privacy.Simulator.Arithmetic.SharedFiniteSourceDecision
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineCost
import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingSourceJoint
import Proof.Privacy.Simulator.Arithmetic.CompiledSetupJoint
import Proof.Privacy.Simulator.Arithmetic.OfflineInitialMemory
import Proof.Privacy.Simulator.Arithmetic.GateLoopJointMemory
import Proof.Privacy.Simulator.Arithmetic.GateLoopJointCaller
import Proof.Privacy.Simulator.Arithmetic.CompiledPublicAllowance
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineValid
import Proof.Privacy.Simulator.Arithmetic.CompiledSetupProtocol
import Proof.Privacy.Simulator.Arithmetic.CompiledQueryCost
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicJointReady
import Proof.Privacy.Simulator.Arithmetic.GateDriverJointPrivate
import Proof.Privacy.Simulator.Arithmetic.GateDriverJointMemory
import Proof.Privacy.Simulator.Arithmetic.SharedCommandListProgram
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineLink
import Proof.Privacy.Simulator.Arithmetic.OnlineMachinePrepare
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineNull
import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingWitness
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicFixedHistory
import Proof.Privacy.Simulator.Arithmetic.EncLinkTypedSource
import Proof.Privacy.Simulator.Arithmetic.EncLinkCompleteMemory
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHistory
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicNonfixed
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicWord
import Proof.Privacy.Simulator.Arithmetic.SharedSourceDecisionBound
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicJointSource
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicFamily
import Proof.Privacy.Simulator.Arithmetic.SharedHistoryRecord
import Proof.Privacy.Simulator.Arithmetic.EncLinkComplete
import Proof.Privacy.Simulator.Arithmetic.EncLinkSource
import Proof.Privacy.Simulator.Arithmetic.EncLinkDataInitialize
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineBranch
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineFinish
import Proof.Privacy.Simulator.Arithmetic.OnlineMachinePrefix
import Proof.Privacy.Simulator.Arithmetic.CheckedSlotCoupling
import Proof.Privacy.Simulator.Arithmetic.CheckedSlotJointMemory
import Proof.Privacy.Simulator.Arithmetic.SharedAdaptiveProgram
import Proof.Privacy.Simulator.Arithmetic.CompiledQueryResponse
import Proof.Privacy.Simulator.Arithmetic.EncLinkLoopSource
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineLinear
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineComponents
import Proof.Privacy.Simulator.Arithmetic.CompiledMachineRun
import Proof.Privacy.Simulator.Arithmetic.ParsedProgramSource
import Proof.Privacy.Simulator.Arithmetic.RetargetScheduleMemory
import Proof.Privacy.Simulator.Arithmetic.RetargetFrame
import Proof.Privacy.Simulator.Arithmetic.RetargetCurveSource
import Proof.Privacy.Simulator.Arithmetic.RetargetPointSource
import Proof.Privacy.Simulator.Arithmetic.EncLinkArrayFrame
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineLabels
import Proof.Privacy.Simulator.Arithmetic.EncLinkDataMemory
import Proof.Privacy.Simulator.Arithmetic.EncLinkCoordinateStep
import Proof.Privacy.Simulator.Arithmetic.EncLinkReindex
import Proof.Privacy.Simulator.Arithmetic.EncLinkOutput
import Proof.Privacy.Simulator.Arithmetic.ProgramCutoff
import Proof.Privacy.Simulator.Arithmetic.CheckedSlotGlobalPreservation
import Proof.Privacy.Simulator.Arithmetic.ProgramReindex
import Proof.Privacy.Simulator.Arithmetic.CheckedProgramSource
import Proof.Privacy.Simulator.SharedChallengePrivacy
import Proof.Privacy.Simulator.Arithmetic.CheckedSlotFamilyReady
import Proof.Privacy.Simulator.Arithmetic.HistoryMemory
import Proof.Privacy.Bounds.SharedMachineArithmetic
import Proof.Privacy.Simulator.Arithmetic.RespondSource
import Proof.Privacy.Simulator.Arithmetic.CompiledBlockAllowance
import Proof.Privacy.Simulator.Arithmetic.RetargetSchedule
import Proof.Privacy.Simulator.Arithmetic.GateDriverPrepared
import Proof.Privacy.Simulator.Arithmetic.GateSchedule
import Proof.Privacy.Simulator.Arithmetic.EncLinkLoopMemory
import Proof.Privacy.Simulator.Arithmetic.EncLinkLoopRun
import Proof.Privacy.Simulator.Arithmetic.EncLinkInitializeMemory
import Proof.Privacy.Simulator.Arithmetic.EncLinkPhysicalIndex
import Proof.Privacy.Simulator.Arithmetic.EncLinkCost
import Proof.Privacy.Simulator.Arithmetic.EncLinkProgram
import Proof.Privacy.Simulator.Arithmetic.RunReserve
import Proof.Privacy.Simulator.Arithmetic.GateDriverCost
import Proof.Privacy.Simulator.Arithmetic.SharedSourceCutoff
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicOperational
import Proof.Privacy.Simulator.Arithmetic.PublicHistoryResultPhysical
import Proof.Privacy.Simulator.Arithmetic.CheckedSlotBlock
import Proof.Privacy.SharedConcreteAdaptivePrivacy
import Proof.Privacy.Simulator.Arithmetic.PhaseDispatch
import Proof.Privacy.Simulator.Arithmetic.EncLinkTail
import Proof.Privacy.Simulator.Arithmetic.HashPrivate
import Proof.Privacy.Simulator.Arithmetic.OracleHistoryFrame
import Proof.Privacy.Simulator.Arithmetic.InternalForwardReturn
import Proof.Privacy.Simulator.Arithmetic.InternalForwardPrivate
import Proof.Privacy.Simulator.Arithmetic.EncLinkRead
import Proof.Privacy.Simulator.Arithmetic.EncLinkControl
import Proof.Privacy.Simulator.Arithmetic.EncLinkBlock
import Proof.Privacy.Simulator.Arithmetic.EncLinkIndex
import Proof.Privacy.Simulator.Arithmetic.PublicHistoryRun
import Proof.Privacy.Simulator.Arithmetic.HistoryFreshMachine
import Proof.Privacy.Bounds.SharedSourceEventBound
import Proof.Privacy.Source.SharedCombinedRatio
import Proof.Privacy.Collision.SharedPipelinePrefixBadMass
import Proof.Privacy.Simulator.Arithmetic.EncLinkArithmetic
import Proof.Privacy.Simulator.Arithmetic.InternalForwardSource
import Proof.Privacy.Simulator.Arithmetic.HistoryAppend
import Proof.Privacy.Simulator.Arithmetic.GateDirectiveScratch
import Proof.Privacy.Simulator.Arithmetic.GateDirectiveSource
import Proof.Privacy.Simulator.Arithmetic.SelectedLabelStoreMachine
import Proof.Privacy.Source.SharedFullTranscriptPrefix
import Proof.Privacy.Source.Invalid.SharedCurveGuardFromPipeline
import Proof.Privacy.Source.Invalid.SharedCurveSupportedRatio
import Proof.Privacy.Source.Valid.SharedPipelineSupportedRatio
import Proof.Privacy.Source.Valid.SharedPipelinePhaseSum
import Proof.Privacy.Source.SharedRetainedTableAlignment
import Proof.Privacy.Transcript.SharedGateEndpoint
import Proof.Privacy.Source.Invalid.SharedCurvePhaseMass
import Proof.Privacy.Source.SharedNonfixedSourceMass
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerOperational
import Proof.Privacy.Simulator.Arithmetic.HashLiftMachine
import Proof.Privacy.Simulator.Arithmetic.GateBlocksMachine
import Proof.Privacy.Source.Valid.SharedPipelineEndpointRatio
import Proof.Privacy.Source.Valid.SharedPipelineSourceView
import Proof.Privacy.Source.SharedFullGateSourceMass
import Proof.Privacy.Source.Invalid.SharedCurveEndpointRatio
import Proof.Privacy.Simulator.Arithmetic.GateRetargetMachine
import Proof.Privacy.Simulator.Arithmetic.PolynomialInput
import Proof.Privacy.Simulator.Arithmetic.SparseInverseMemory
import Proof.Privacy.Simulator.Arithmetic.OracleMemoryCongr
import Proof.Privacy.Simulator.Arithmetic.PermutationOtherOracle
import Proof.Privacy.Simulator.Arithmetic.HashOtherOracle
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerRam
import Proof.Privacy.Source.SharedIdealGateCoin
import Proof.Privacy.Source.SharedSimulatorSourceDistribution
import Proof.Privacy.Source.Invalid.SharedCurveGlobalEventRatio
import Proof.Privacy.Collision.SharedAdaptivePointBad
import Proof.Privacy.Collision.SharedHiddenLinkBad
import Proof.Privacy.Bounds.SharedAdaptiveArithmetic
import Proof.Privacy.Simulator.Arithmetic.StoredForwardSource
import Proof.Privacy.Simulator.Arithmetic.StoredInverseSource
import Proof.Privacy.Simulator.Arithmetic.HashSourceMemory
import Proof.Privacy.Distribution.SharedAdaptiveGateMask
import Proof.Privacy.Source.Valid.SharedPipelineEventRatio
import Proof.Privacy.Distribution.SharedHashRounding
import Proof.Privacy.Source.Invalid.SharedInvalidMaskEntrance
import Proof.Privacy.Bounds.SharedCurveLoss
import Proof.Privacy.Simulator.SharedGameDistribution
import Proof.Privacy.Simulator.Arithmetic.OutputTargetsMachine
import Proof.Privacy.Simulator.Arithmetic.SelectedLabelsProtocol
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerTyped
import Proof.Privacy.Simulator.Arithmetic.OfflineMachineProtocol
import Proof.Privacy.Simulator.Arithmetic.HashQueryMemory
import Proof.Privacy.Simulator.Arithmetic.PermutationFrame
import Proof.Privacy.Simulator.Arithmetic.StoredForwardFrame
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerCounts
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerBits
import Proof.Privacy.Source.Invalid.SharedCurveEventRatio
import Proof.Privacy.Source.SharedRetainedContext
import Proof.Privacy.Source.Invalid.SharedCurveGlobalRatio
import Proof.Privacy.Transcript.SharedIdealTranscript
import Proof.Privacy.Simulator.Arithmetic.OutputTargetRows
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerRun
import Proof.Privacy.Simulator.Arithmetic.HashProgram
import Proof.Privacy.Simulator.Arithmetic.FreshQueryMemory
import Proof.Privacy.Simulator.Arithmetic.OverlayMemory
import Proof.Privacy.Simulator.Arithmetic.OfflineWireSource
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerTail
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerDispatch
import Proof.Privacy.Source.SharedRealSourceLower
import Proof.Privacy.Source.SharedPipelineSourceRatio
import Proof.Privacy.Source.SharedCurveIndependentRatio
import Proof.Privacy.Source.SharedHiddenEncSource
import Proof.Privacy.Collision.SharedReconstructedFreshness
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerCode
import Proof.Privacy.Simulator.Arithmetic.OverlayScan
import Proof.Privacy.Simulator.Arithmetic.PointHornerSource
import Proof.Privacy.Simulator.Arithmetic.ClampPoint
import Proof.Privacy.Simulator.Arithmetic.OnlineInputReturn
import Proof.Privacy.Simulator.Arithmetic.PublicWireProtocol
import Proof.Privacy.Source.SharedFullSourceRestTransport
import Proof.Privacy.Source.SharedRealSourceSum
import Proof.Privacy.Source.SharedHiddenSourceTransport
import Proof.Privacy.Source.SharedRetainedProgramRatio
import Proof.Privacy.Source.SharedQueryBudget
import Proof.Privacy.Programming.SharedScheduleFreshness
import Proof.Privacy.Simulator.Arithmetic.OnlineSampling
import Proof.Privacy.Simulator.Arithmetic.StoredForward
import Proof.Privacy.Simulator.Arithmetic.StoredInverse
import Proof.Privacy.Simulator.Arithmetic.InstallFreshLayout
import Proof.Privacy.Simulator.Arithmetic.OnlineInputProtocol
import Proof.Privacy.Simulator.Arithmetic.QueryInputReturn
import Proof.Privacy.Simulator.Arithmetic.SamplerBatch
import Proof.Privacy.Simulator.Arithmetic.OracleMetadata
import Proof.Privacy.Simulator.Arithmetic.SwapMetadata
import Proof.Privacy.Simulator.Arithmetic.KnownQueryBlock
import Proof.Privacy.Source.SharedRetainedPostquery
import Proof.Privacy.Programming.SharedScheduleCounts
import Proof.Privacy.Simulator.Arithmetic.FreshQuerySource
import Proof.Privacy.Programming.SharedScheduleRecords
import Proof.Privacy.Simulator.Arithmetic.QueryInputProtocol
import Proof.Privacy.Simulator.Arithmetic.PointSamplerBlock
import Proof.Privacy.Simulator.Arithmetic.FreshQuery
import Proof.Privacy.Simulator.Arithmetic.PrivateSchedule
import Proof.Privacy.Simulator.Arithmetic.SamplerBatchMemory
import Proof.Privacy.Source.SharedRetainedMass
import Proof.Privacy.Source.SharedActiveMass
import Proof.Privacy.Distribution.SharedProgramQueryMass
import Proof.Privacy.Simulator.Arithmetic.ByteOutputWire
import Proof.Privacy.Simulator.Arithmetic.PrivateSamplers
import Proof.Privacy.Simulator.Arithmetic.OracleScratch
import Proof.Privacy.Simulator.Arithmetic.ByteOutput
import Proof.Privacy.Simulator.Arithmetic.WireCodec
import Proof.Privacy.Simulator.Arithmetic.PointSampler
import Proof.Privacy.Simulator.Arithmetic.KnownQuery
import Proof.Privacy.Simulator.Arithmetic.PairMemory
import Proof.Privacy.Simulator.Arithmetic.SwapBlock
import Proof.Privacy.Bounds.CombinedPrivacy
import Proof.Privacy.Source.SharedRetainedSource
import Proof.Privacy.Source.SharedTranscriptMass
import Proof.Privacy.Collision.SharedPrequeryBound
import Proof.Privacy.Distribution.SharedProgrammingDistribution
import Proof.Privacy.Simulator.Arithmetic.SwapTable
import Proof.Privacy.Source.SharedAdaptiveRatio
import Proof.Privacy.Simulator.Arithmetic.WordInputBlock
import Proof.Privacy.Simulator.Arithmetic.TableBlock
import Proof.Privacy.Source.SharedBucketCounts
import Proof.Privacy.Simulator.Arithmetic.RuntimeSampler
import Proof.Privacy.Simulator.Arithmetic.WordOutput
import Proof.Privacy.Collision.SharedCrossBranchBound
import Proof.Privacy.Simulator.Arithmetic.SampleToRam
import Proof.Privacy.Simulator.SharedOracleProgram
import Proof.Privacy.Simulator.SharedSimulator
import Proof.Privacy.Programming.SharedGate
import Proof.Privacy.Collision.SharedGateAssignment
import Proof.Privacy.Collision.SharedBranchCollision
import Proof.Privacy.Simulator.SimulatorActualImplementation
import Proof.Privacy.Simulator.SimulatorChallengePrivacy
import Construction
import Solution
import Proof.Correctness
import Proof.Privacy.ConcreteSmallSourceRatio
import Proof.Privacy.PaperConstruction
import Proof.Privacy.Simulator.SimulatorTotalImplementation
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerRun
import Proof.Privacy.Simulator.Arithmetic.PhaseMachineRun
import Proof.Privacy.Simulator.Arithmetic.OracleFamilyInitial
import Proof.Privacy.Simulator.Arithmetic.OracleFamilySource
import Proof.Privacy.Simulator.Arithmetic.OracleFamilyCutoff
import Proof.Privacy.Simulator.Arithmetic.OracleFamilyLaw
import Proof.Privacy.Simulator.SharedMachineInitial
import Proof.Privacy.Simulator.Arithmetic.EncLinkIteration
import Proof.Privacy.Simulator.Arithmetic.EncLinkFrame
import Proof.Privacy.Simulator.Arithmetic.EncLinkState

namespace Kriterion.ArgoMAC.Security

open BN254

/-- This is the adaptive-privacy field of the obligation for the ArgoMAC construction. -/
def AdaptivePrivacy : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field),
    ∃ simulator : GarbledCircuit.Simulator AffineInput (Option (@Point field)) Pipeline.Table
      Garbling.Labels Garbling.Topology CircuitSimulatorState,
      GarbledCircuit.ConcreteAdaptivePrivacy (Aux := Unit)
        (@Garbling.garbledCircuit field group construction) Garbling.topology simulator
        (@uniformRandomTape Garbling.Randomness (@Fintype.ofFinite _ inferInstance)
          (Seed.randomness 0))
        Garbling.oracleHandler circuitSimulatorOracleHandler 100

/-- The checked simulator gives the required universal privacy bound. -/
theorem adaptivePrivacy : AdaptivePrivacy := by
  intro field group
  letI := field
  letI := group
  refine ⟨concreteCircuitSimulator, ?_⟩
  have instances : (@Fintype.ofFinite Garbling.Randomness inferInstance) =
      garblingRandomnessFintype := Subsingleton.elim _ _
  have tapes : @uniformRandomTape Garbling.Randomness (@Fintype.ofFinite _ inferInstance)
      (Seed.randomness 0) = randomTape (Seed.randomness 0) := by
    unfold uniformRandomTape randomTape
    rw [Cryptography.uniformTape_eq, instances]
  rw [tapes]
  exact concreteAdaptivePrivacy (Seed.randomness 0)

/-- The circuit topology does not depend on the scalar. -/
theorem topologyConstant (first second : NonZeroScalar) :
    Garbling.topology first = Garbling.topology second := rfl

end Kriterion.ArgoMAC.Security
