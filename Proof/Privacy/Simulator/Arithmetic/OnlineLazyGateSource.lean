import Proof.Privacy.Simulator.Arithmetic.OnlineLazyMemory
import Proof.Privacy.Simulator.Arithmetic.OnlineLazyRun
import Proof.Privacy.Simulator.Arithmetic.SharedGateLoopCommands
import Proof.Privacy.Simulator.Arithmetic.GateLoopBits

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorSampling Security.SharedSimulatorMachine
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
attribute [local irreducible] lazyGateLoopResults onlineFinalMemory

/-- The curve loop executes its typed strict program list. -/
theorem LazyOnlineGateData.curveSource [FieldCertificate] [GroupCertificate]
    {coin : OfflineCoin} {input : AffineInput} {output : Point}
    {sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)} {mac : InputMac} {memory : Memory}
    (ready : LazyOnlineGateData coin input output sample mac memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    (lazyGateLoopResults curveGatePlan 1270 0 (onlineGateInitial memory) oracle).map (fun result => result.2.1) =
      OperationalOracle.strictCommands oracle
        ((scheduleCommands (((sharedOfflineFrame coin).selectedCurve input).schedule input
          ((sharedOfflineFrame coin).labels input).inputMac)).map sharedCommand) := by
  have setup := onlineOriginalSetup_state memory
  have source := lazyGateLoopResults_source curveGatePlan
    (curveDirectiveAt ((sharedOfflineFrame coin).selectedCurve input) input ((sharedOfflineFrame coin).labels input).inputMac)
    (fun index => coin.1.curve.quotients ⟨index.val / 254, by have := index.isLt; omega⟩
      ⟨index.val % 254, Nat.mod_lt _ (by decide)⟩)
    1270 0 (onlineGateInitial memory) (onlineGateInitial memory) oracle (by decide)
    (GatePrivateAgreement.refl _) ready.curvePlan (by
      intro index
      simpa only [curveGatePlan, Vector.getElem_ofFn, onlineGateInitial] using curveGateCode_private (onlineGateInitial memory)
        ⟨index.val / 254, by have := index.isLt; omega⟩ ⟨index.val % 254, Nat.mod_lt _ (by decide)⟩
        onlineOriginalBase setup.2.2.1 setup.2.2.2.1 setup.2.2.2.2 (by decide) (by decide))
  simpa only [sharedDirectiveLoop_list, curveDirectiveAt_schedule] using source

/-- The point loop executes its typed strict program list. -/
theorem LazyOnlineGateData.pointSource [FieldCertificate] [GroupCertificate]
    {coin : OfflineCoin} {input : AffineInput} {output : Point}
    {sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)} {mac : InputMac} {memory : Memory}
    (ready : LazyOnlineGateData coin input output sample mac memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    (lazyGateLoopResults pointGatePlan 277368 0 (onlinePointGateInitial memory) oracle).map (fun result => result.2.1) =
      OperationalOracle.strictCommands oracle
        ((scheduleCommands (pointGateSchedule
          ((sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2)
          input mac)).map sharedCommand) := by
  have setup := onlinePointSetup_state (onlineTagMemory memory)
  have source := lazyGateLoopResults_source pointGatePlan
    (pointDirectiveAt ((sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2) input mac)
    (fun index => Classical.choose (ready.pointPlan index))
    277368 0 (onlinePointGateInitial memory) (onlinePointGateInitial memory) oracle (by decide)
    (GatePrivateAgreement.refl _) (fun index => Classical.choose_spec (ready.pointPlan index)) (by
      intro index
      simpa only [pointGatePlan, Vector.getElem_ofFn, onlinePointGateInitial] using pointGateCode_private (onlinePointGateInitial memory)
        ⟨index.val / 3048, by
          have bound := index.isLt
          have rowCount : FieldMacToECMac.outputMacCount = 91 := rfl
          omega⟩
        ⟨index.val % 3048 / 254, by omega⟩ ⟨index.val % 254, by omega⟩
        onlineLinkedBase setup.2.2.1 setup.2.2.2.1 setup.2.2.2.2 (by decide) (by decide))
  simpa only [sharedDirectiveLoop_list, pointDirectiveAt_schedule] using source


attribute [local irreducible] lazyOnlineValidGateResult

/-- The curve loop retains every typed point input. -/
theorem LazyOnlineGateData.afterCurve [FieldCertificate] [GroupCertificate]
    {coin : OfflineCoin} {input : AffineInput} {output : Point}
    {sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)} {mac : InputMac} {memory : Memory}
    (ready : LazyOnlineGateData coin input output sample mac memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) (curve)
    (success : lazyGateLoopResults curveGatePlan 1270 0 (onlineGateInitial memory) oracle = some curve) :
    LazyOnlineGateData coin input output sample mac curve.1 := by
  have agreement := GatePrivateAgreement.afterLazyLoop curveGatePlan 1270 0
    (onlineGateInitial memory) (onlineGateInitial memory) oracle (GatePrivateAgreement.refl _) curve success
  have bits := lazyGateLoopResults_bits curveGatePlan 1270 0 (onlineGateInitial memory) oracle curve success
  apply ready.frame
  · intro cell lower upper
    exact (agreement.words cell lower upper).trans (congrFun (onlineOriginalSetup_state memory).1 _)
  · exact congrFun (bits.trans (onlineOriginalSetup_state memory).2.1) 3

private theorem optionBind_projection {A B S T : Type} (first : Option A) (next : A → Option B)
    (projectA : A → S) (projectB : B → T) (source : S → Option T)
    (law : ∀ value, first = some value → (next value).map projectB = source (projectA value)) :
    (first.bind next).map projectB = (first.map projectA).bind source := by
  cases first with
  | none => rfl
  | some value => exact law value rfl

/-- Both gate loops have the exact ordered strict schedule. -/
theorem lazyOnlineValidGateResult_source [FieldCertificate] [GroupCertificate]
    {coin : OfflineCoin} {input : AffineInput} {output : Point}
    {sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)} {mac : InputMac} {memory : Memory}
    (ready : LazyOnlineGateData coin input output sample mac memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    (lazyOnlineValidGateResult memory oracle).map (fun result => result.2.1) =
      OperationalOracle.strictCommands oracle
        ((scheduleCommands (pipelineGateSchedule ((sharedOfflineFrame coin).selectedCurve input)
          ((sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2)
          input ((sharedOfflineFrame coin).labels input).inputMac mac)).map sharedCommand) := by
  let commands := fun (current : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) => OperationalOracle.strictCommands current
    ((scheduleCommands (pointGateSchedule
      ((sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2)
      input mac)).map sharedCommand)
  have projected := optionBind_projection
    (lazyGateLoopResults curveGatePlan 1270 0 (onlineGateInitial memory) oracle)
    (fun curve => lazyGateLoopResults pointGatePlan 277368 0 (onlinePointGateInitial curve.1) curve.2.1)
    (fun result => result.2.1) (fun result => result.2.1) commands
    (fun curve reached => (ready.afterCurve oracle curve reached).pointSource curve.2.1)
  rw [ready.curveSource oracle] at projected
  simpa only [lazyOnlineValidGateResult, onlineGateInitial, onlinePointGateInitial, commands,
    pipelineGateSchedule, scheduleCommands, List.flatMap_append, List.map_append,
    OperationalOracle.strictCommands_append, Option.map_bind, Option.map_map,
    Option.pure_def, Option.map_some, Function.comp_def, Bind.bind, Option.map_eq_bind, Option.bind_assoc, Option.bind_some] using projected

/-- Both gate loops retain the selected label parser's private inputs. -/
theorem lazyOnlineValidGateResult_labels [FieldCertificate] [GroupCertificate]
    {coin : OfflineCoin} {input : AffineInput} {output : Point}
    {sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)} {mac : InputMac} {memory : Memory}
    (ready : LazyOnlineGateData coin input output sample mac memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) (result)
    (success : lazyOnlineValidGateResult memory oracle = some result) :
    GarbledCircuit.SimulatorProtocol.words 128 508 (result.1.bits 3) =
      some (Lamport.selectedLabels (coin.2.1.encodeAffine input)) := by
  unfold lazyOnlineValidGateResult at success
  dsimp only [Bind.bind] at success
  obtain ⟨curve, curveSuccess, point, pointSuccess, equal⟩ :=
    (by simpa only [Option.bind_eq_some_iff] using success)
  cases equal
  have curveReady := ready.afterCurve oracle curve curveSuccess
  have agreement := GatePrivateAgreement.afterLazyLoop pointGatePlan 277368 0
    (onlinePointGateInitial curve.1) (onlinePointGateInitial curve.1) curve.2.1
    (GatePrivateAgreement.refl _) point pointSuccess
  have bits := lazyGateLoopResults_bits pointGatePlan 277368 0 (onlinePointGateInitial curve.1) curve.2.1 point pointSuccess
  have setup := onlinePointSetup_state (onlineTagMemory curve.1)
  have pointReady : LazyOnlineGateData coin input output sample mac point.1 := by
    apply curveReady.frame
    · intro cell lower upper
      exact (agreement.words cell lower upper).trans (congrFun setup.1 _)
    · exact congrFun (bits.trans setup.2.1) 3
  exact onlineFinalMemory_keyProtocol point.1 coin.2.1 input pointReady.keys pointReady.coordinates pointReady.empty

/-- The parsed gate result contains the selected labels and exact strict oracle. -/
theorem lazyOnlineValidGateResult_parsed [FieldCertificate] [GroupCertificate]
    {coin : OfflineCoin} {input : AffineInput} {output : Point}
    {sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)} {mac : InputMac} {memory : Memory}
    (ready : LazyOnlineGateData coin input output sample mac memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    ((lazyOnlineValidGateResult memory oracle).bind fun result =>
      (GarbledCircuit.SimulatorProtocol.words 128 508 (result.1.bits 3)).map fun labels => (labels, result.2.1)) =
      (OperationalOracle.strictCommands oracle
        ((scheduleCommands (pipelineGateSchedule ((sharedOfflineFrame coin).selectedCurve input)
          ((sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2)
          input ((sharedOfflineFrame coin).labels input).inputMac mac)).map sharedCommand)).map
        (fun updated => (Lamport.selectedLabels (coin.2.1.encodeAffine input), updated)) := by
  rw [← lazyOnlineValidGateResult_source ready oracle, Option.map_map]
  cases reached : lazyOnlineValidGateResult memory oracle with
  | none => rfl
  | some result =>
    simp only [Option.bind_some, Option.map_some, Function.comp_def]
    rw [lazyOnlineValidGateResult_labels ready oracle result reached]
    rfl

/-- Every supported lazy link has the same typed gate inputs. -/
theorem lazyOnline_gateData [FieldCertificate] [GroupCertificate]
    (memory : Memory) (input : AffineInput) (output : Point) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (empty : memory.bits 3 = []) (sampled : Memory × Nat)
    (supported : sampled ∈ (onlineSamplingMemory 256
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) [])))).support)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) (linked)
    (member : linked ∈ (lazyEncLinkSamples (onlinePreparedMemory sampled.1 output
      (onlineSamplingCoin 256 (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled)) oracle).support) :
    let sample := onlineSamplingCoin 256
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled
    LazyOnlineGateData coin input output sample (encLinkOutputMac linked.1.1 onlineLinkedBase) linked.1.1 := by
  obtain ⟨complete, same⟩ := lazyEncLinkSamples_witness _ oracle linked member
  rw [← same]
  exact eagerOnline_gateData memory input output coin stored empty sampled supported complete

end
end Kriterion.ArgoMAC.ArithmeticSimulator
