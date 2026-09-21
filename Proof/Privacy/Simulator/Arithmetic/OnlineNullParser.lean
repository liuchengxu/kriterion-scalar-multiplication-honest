import Proof.Privacy.Simulator.Arithmetic.OnlineNullJointMemory
import Proof.Privacy.Simulator.Arithmetic.GateLoopBits

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorSampling Security.SharedSimulatorMachine
noncomputable section
attribute [local irreducible] gateLoopSamples onlineNullMemoryJoint

/-- Each accepted curve joint retains an actual gate-loop sample. -/
theorem onlineCurveJoint_actual [FieldCertificate] (attempts limit : Nat)
    (request : CurveGateRequest) (input : AffineInput) (mac : InputMac) (memory : Memory) (state : SharedOracleSource)
    (ready : GateLoopCoupledReady curveGatePlan
      (fun gate => sharedDirectiveSlot (curveDirectiveAt request input mac gate))
      (fun gate => !(curveDirectiveAt request input mac gate).bit) attempts 1270 0 limit memory state)
    (room : 256 + 2 * (limit + 3810) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256)
    (result : GateLoopJointResult)
    (supported : some result ∈ (onlineCurveJoint attempts request input mac memory state).support) :
    result.1 ∈ (gateLoopSamples curveGatePlan attempts 1270 0 memory).support := by
  have projected : some result.1 ∈ ((onlineCurveJoint attempts request input mac memory state).map
      (Option.map Prod.fst)).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨some result, supported, rfl⟩
  rw [show onlineCurveJoint attempts request input mac memory state = gateLoopCoupled curveGatePlan
      (fun gate => sharedDirectiveSlot (curveDirectiveAt request input mac gate)) attempts 1270 0 memory state from rfl,
    gateLoopCoupled_machine curveGatePlan _ _ attempts 1270 0 limit memory state ready room attemptFits] at projected
  obtain ⟨actual, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp projected
  split at same
  · have equal := Option.some.inj same
    exact equal ▸ member
  · cases same

/-- The accepted absent-output joint emits the exact original selected labels. -/
theorem onlineNullMemoryJoint_keyProtocol [FieldCertificate] (attempts limit : Nat)
    (memory : Memory) (input : AffineInput) (coin : OfflineCoin) (state : SharedOracleSource)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 3810) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256)
    (empty : (onlineNullGateInitial (onlineCurveMemory memory input none [])).bits 3 = [])
    (result : OnlineJointMemoryResult)
    (supported : some result ∈ (onlineNullMemoryJoint attempts (sharedOfflineFrame coin) input memory state).support) :
    GarbledCircuit.SimulatorProtocol.words 128 508 (result.2.1.1.bits 3) =
      some (Lamport.selectedLabels result.1.inputMac) := by
  have retained := onlineNullMemoryJoint_memory attempts limit memory input coin state stored represented room result supported
  unfold onlineNullMemoryJoint at supported
  obtain ⟨draw, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases draw with
  | none => simp at same
  | some draw =>
      have equal := Option.some.inj same
      subst result
      have ready := onlineNull_ready attempts limit memory input none [] coin state stored represented room
      have actual := onlineCurveJoint_actual attempts limit _ _ _ _ state ready room attemptFits draw member
      have bits := gateLoopSamples_bits curveGatePlan attempts 1270 0 _ draw.1 actual
      change GarbledCircuit.SimulatorProtocol.words 128 508
        ((onlineFinalMemory (onlineTagMemory draw.1.2.1)).bits 3) = _
      apply onlineFinalMemory_keyProtocol _ coin.2.1 input
      · simpa only [onlineFinalMemory_ram] using retained.2.2.1
      · simpa only [onlineFinalMemory_ram] using retained.2.2.2
      · change draw.1.2.1.bits 3 = []
        rw [bits, empty]

/-- Every absent-output cutoff has an empty label response. -/
theorem compiledOnlineNullSamples_failure [FieldCertificate] (attempts : Nat) (memory : Memory)
    (input : AffineInput)
    (empty : (onlineNullGateInitial (onlineCurveMemory memory input none [])).bits 3 = [])
    (result : Configuration 290305300 × Nat)
    (supported : result ∈ (compiledOnlineNullSamples attempts memory input []).support)
    (failed : result.1.pc ≠ 290305298) :
    GarbledCircuit.SimulatorProtocol.words 128 508 (result.1.memory.bits 3) = none := by
  simp only [compiledOnlineNullSamples, PMF.map_comp, Function.comp_def] at supported
  obtain ⟨raw, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have bits := gateLoopSamples_bits curveGatePlan attempts 1270 0 _ raw member
  cases success : raw.1
  · simp only [onlineNullGateResult, success, Bool.false_eq_true, ↓reduceIte]
    rw [bits, empty]
    rfl
  · simp only [onlineNullGateResult, success, ↓reduceIte] at failed
    exact False.elim (failed rfl)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
