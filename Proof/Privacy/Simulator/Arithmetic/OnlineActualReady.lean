import Proof.Privacy.Simulator.Arithmetic.OnlineLinkedGateReady
import Proof.Privacy.Simulator.Arithmetic.OnlineNullJointMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorSampling Security.SharedSimulatorMachine
noncomputable section
attribute [local irreducible] GateLoopReady GateLoopCoupledReady gateLoopSamples

private theorem gateCapacity (limit cap : Nat) (bounded : limit + 3 * 278638 ≤ cap)
    (room : 256 + 2 * (cap + 1) < 2 ^ 110) :
    256 + 2 * (limit + 3810) < 2 ^ 110 ∧
    256 + 2 * (limit + 3 * 278638) < 2 ^ 110 ∧
    limit + 3 * 1270 ≤ cap ∧ (limit + 3 * 1270) + 3 * 277368 ≤ cap := by omega

private theorem linkedCapacity (limit cap : Nat) (bounded : limit + 836422 ≤ cap)
    (room : 2 * (cap + 508) + 256 < 2 ^ 110) :
    256 + 2 * (limit + 1) < 2 ^ 110 ∧ limit ≤ cap ∧ 2 * (limit + 508) + 256 < 2 ^ 110 ∧
    (limit + 508) + 3 * 278638 ≤ cap ∧ 256 + 2 * (cap + 1) < 2 ^ 110 := by omega

/-- The linked source supplies the actual curve and point loop reserves. -/
theorem OnlineLinkedGateMemory.actualReady [FieldCertificate] [GroupCertificate]
    (attempts cap : Nat) {coin : OfflineCoin} {input : AffineInput} {output : Point}
    {sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)} {memory : Memory}
    {state : SharedOracleSource} {limit : Nat}
    (ready : OnlineLinkedGateMemory coin input output sample memory state limit)
    (tag : memory.ram (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0)
    (bounded : limit + 3 * 278638 ≤ cap) (room : 256 + 2 * (cap + 1) < 2 ^ 110)
    (attemptFits : attempts < 2 ^ 256) : OnlineGateReady attempts cap memory := by
  obtain ⟨curveRoom, completeRoom, curveBound, pointBound⟩ := gateCapacity limit cap bounded room
  have curve := ready.curveReady attempts curveRoom
  refine ⟨gateLoopReady_of_coupled curveGatePlan _ _ attempts 1270 0 limit cap _ state curve curveBound room attemptFits, ?_⟩
  intro result supported accepted
  obtain ⟨next, member⟩ := onlineCurveJoint_witness attempts limit _ _ _ _ state curve curveRoom attemptFits result supported accepted
  have initial : SharedSourceMemory (onlineGateInitial memory) state limit :=
    ready.represented.ramEq (onlineOriginalSetup_state memory).1
  have saved := gateLoopCoupled_memory curveGatePlan _ _ attempts 1270 0 limit _ state initial curve curveRoom (result, next) member
  refine ⟨?_, gateLoopReady_of_coupled pointGatePlan _ _ attempts 277368 0 (limit + 3 * 1270) cap _ next
    (ready.pointReady attempts completeRoom (result, next) member) pointBound room attemptFits⟩
  rw [saved.2.2 (onlineInputBase + 2) (by decide) (by decide)]
  change (executeLinear onlineOriginalSetup memory).ram _ ≠ _
  rw [(onlineOriginalSetup_state memory).1]
  exact tag

/-- The common prefix retains the exact selected output point. -/
theorem selectedOutputPoint_curve [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Point) : selectedOutputPoint (onlineCurveMemory memory input (some output) []).ram
      (BitVec.ofNat 256 onlineInputBase) = some output := by
  have same : selectedOutputPoint (onlineCurveMemory memory input (some output) []).ram
      (BitVec.ofNat 256 onlineInputBase) = selectedOutputPoint (onlineReadMemory memory input (some output) []).ram
      (BitVec.ofNat 256 onlineInputBase) := by
    have kept (offset : Nat) (bound : offset < 5) :
        (onlineCurveMemory memory input (some output) []).ram (BitVec.ofNat 256 (onlineInputBase + offset)) =
        (onlineReadMemory memory input (some output) []).ram (BitVec.ofNat 256 (onlineInputBase + offset)) :=
      onlineCurveMemory_input memory input (some output) [] ⟨offset, bound⟩
    unfold selectedOutputPoint
    apply readPoint_congr
    all_goals
      simp only [show (2 : Word) = BitVec.ofNat 256 2 from rfl,
        show (3 : Word) = BitVec.ofNat 256 3 from rfl, show (4 : Word) = BitVec.ofNat 256 4 from rfl,
        ← BitVec.ofNat_add]
      rw [kept 2 (by decide), kept 3 (by decide), kept 4 (by decide)]
  exact same.trans (selectedOutputPoint_onlineInput (onlineInputPrepared memory) input output [])

/-- Every actual private sample supplies the complete link and gate readiness conditions. -/
theorem onlineValid_sampledReady [FieldCertificate] [GroupCertificate]
    (attempts limit cap : Nat) (memory : Memory) (input : AffineInput) (output : Point)
    (coin : OfflineCoin) (state : SharedOracleSource)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (represented : SharedSourceMemory memory state limit)
    (bounded : limit + 836422 ≤ cap)
    (room : 2 * (cap + 508) + 256 < 2 ^ 110)
    (hashRoom : 2 * (state.family.hash.length + 1) + 256 < 2 ^ 110)
    (attemptFits : attempts < 2 ^ 256) :
    OnlineSampledReady attempts cap (onlineTagMemory (onlineCurveMemory memory input (some output) []))
      output state.family coin.2.2 [] := by
  obtain ⟨prepareRoom, limitBound, linkRoom, gateBound, gateRoom⟩ := linkedCapacity limit cap bounded room
  intro sampled supported
  let base := onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))
  have pointer : base.registers 10 = BitVec.ofNat 256 onlineSampleBase := rfl
  have ready := onlineValidLink_ready attempts limit memory input output coin state stored represented
    prepareRoom sampled supported
  refine ⟨?_, ⟨ready.represented.family, ready.represented.capacity, ready.operand, ready.outputPointer,
    ?_, ?_, room, hashRoom, ready.wire, ?_⟩⟩
  · rw [onlineSamplingMemory_selectedOutput attempts base sampled.1 sampled.2 pointer supported]
    exact selectedOutputPoint_curve memory input output
  · intro index
    exact (ready.represented.counts.1 index).trans limitBound
  · intro index
    exact (ready.represented.counts.2.1 index).trans limitBound
  · intro linked linkedSupport accepted
    have gateReady := onlineValidLinked_gateMemory attempts limit memory input output coin state stored sampled supported
      ready linkRoom hashRoom linked linkedSupport accepted
    exact gateReady.actualReady attempts cap gateReady.tag gateBound gateRoom attemptFits

private theorem onlineValid_capacity (used : Nat) (small : used < 2 ^ 101) :
    2 * (used + 836931) + 256 < 2 ^ 110 := by
  norm_num at small ⊢
  omega

/-- The actual valid machine closes from the offline array and the reached public-query source. -/
theorem onlineValid_actualRun [FieldCertificate] [GroupCertificate]
    (attempts used : Nat) (memory : Memory) (input : AffineInput) (output : Point)
    (coin : OfflineCoin) (state : SharedOracleSource)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (represented : SharedSourceMemory memory state used)
    (hashes : state.family.hash.length ≤ used) (small : used < 2 ^ 101)
    (attemptFits : attempts < 2 ^ 256)
    (wire : memory.bits 0 = GarbledCircuit.SimulatorProtocol.affine input ++
      GarbledCircuit.SimulatorProtocol.output (some output)) :
    ClosedRun (onlineMachine attempts) 0 memory
      (onlinePrefixCost (some output) + (3 + (1 +
        (onlineSamplingBudget attempts + onlineSelectedReserve attempts (used + 836423) state.family))))
      (onlineValidSamples attempts memory input output state.family coin.2.2 []) := by
  have room := onlineValid_capacity used small
  have sampledReady := onlineValid_sampledReady attempts used (used + 836423) memory input output coin state
    stored represented (by omega) (by simpa only [Nat.add_assoc] using room) (by omega) attemptFits
  exact onlineMachine_valid attempts (used + 836423) memory input output state.family coin.2.2 []
    (by simpa only [List.append_nil] using wire) attemptFits sampledReady

end
end Kriterion.ArgoMAC.ArithmeticSimulator
