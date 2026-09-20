import Proof.Privacy.Simulator.Arithmetic.OnlineCurvePublic
import Proof.Privacy.Simulator.Arithmetic.OnlineKeyBuffers

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorSampling Security.SharedSimulatorMachine
noncomputable section
attribute [local irreducible] GateLoopCoupledReady GateLoopReady gateLoopSamples compiledOnlineNullSamples

private theorem nullSourceRoom (limit : Nat) (room : 256 + 2 * (limit + 3811) < 2 ^ 110) :
    256 + 2 * (limit + 3810) < 2 ^ 110 :=
  lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left 2
    (Nat.add_le_add_left (by decide : 3810 ≤ 3811) limit)) 256) room

/-- Each accepted raw curve sample has an exact shared-source witness. -/
theorem onlineCurveJoint_witness [FieldCertificate] (attempts limit : Nat)
    (request : CurveGateRequest) (input : AffineInput) (mac : InputMac) (memory : Memory) (state : SharedOracleSource)
    (ready : GateLoopCoupledReady curveGatePlan
      (fun gate => sharedDirectiveSlot (curveDirectiveAt request input mac gate))
      (fun gate => !(curveDirectiveAt request input mac gate).bit) attempts 1270 0 limit memory state)
    (room : 256 + 2 * (limit + 3810) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256)
    (result : Bool × Memory × Nat)
    (supported : result ∈ (gateLoopSamples curveGatePlan attempts 1270 0 memory).support)
    (accepted : result.1 = true) :
    ∃ next, some (result, next) ∈ (onlineCurveJoint attempts request input mac memory state).support := by
  have projected : some result ∈ ((gateLoopSamples curveGatePlan attempts 1270 0 memory).map
      (fun result => if result.1 then some result else none)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨result, supported, by simp only [accepted, ↓reduceIte]⟩
  rw [← gateLoopCoupled_machine curveGatePlan _ _ attempts 1270 0 limit memory state ready room attemptFits] at projected
  obtain ⟨joint, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp projected
  cases joint with
  | none => simp at equal
  | some joint =>
      obtain ⟨actual, next⟩ := joint
      have same : actual = result := Option.some.inj equal
      subst actual
      exact ⟨next, member⟩

/-- Every accepted absent-output gate loop retains its zero input tag. -/
theorem onlineNullSamples_tag [FieldCertificate] (attempts limit : Nat)
    (memory : Memory) (input : AffineInput) (coin : OfflineCoin) (state : SharedOracleSource)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 3810) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256)
    (result : Bool × Memory × Nat)
    (supported : result ∈ (gateLoopSamples curveGatePlan attempts 1270 0
      (onlineNullGateInitial (onlineCurveMemory memory input none []))).support)
    (accepted : result.1 = true) : result.2.1.ram (BitVec.ofNat 256 (onlineInputBase + 2)) = 0 := by
  have ready := onlineNull_ready attempts limit memory input none [] coin state stored represented room
  obtain ⟨next, member⟩ := onlineCurveJoint_witness attempts limit _ _ _ _ state ready room attemptFits result supported accepted
  have initial := onlineNullGateInitial_shared memory input none [] state limit represented (by omega)
  have preserved := gateLoopCoupled_memory curveGatePlan _ _ attempts 1270 0 limit _ state initial ready room
    (result, next) member
  rw [preserved.2.2 (onlineInputBase + 2) (by decide) (by decide)]
  change (executeLinear onlineOriginalSetup (onlineTagMemory (onlineCurveMemory memory input none []))).ram _ = _
  rw [(onlineOriginalSetup_state _).1]
  exact onlineCurveMemory_tag memory input none []

/-- The actual offline array and public source close the complete absent-output machine. -/
theorem onlineNullMemoryJoint_run [FieldCertificate] (attempts limit : Nat)
    (memory : Memory) (input : AffineInput) (coin : OfflineCoin) (state : SharedOracleSource)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 3811) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256)
    (wire : memory.bits 0 = GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output none) :
    ClosedRun (onlineMachine attempts) 0 memory
      (onlinePrefixCost none + (6 + (gateDriverRunBudget attempts (limit + 3810) * 1270 + 200666)))
      (compiledOnlineNullSamples attempts memory input []) := by
  have ready := onlineNull_ready attempts limit memory input none [] coin state stored represented (nullSourceRoom limit room)
  simpa only [compiledOnlineNullSamples] using onlineMachine_null attempts (limit + 3810) memory input [] (by simpa using wire) attemptFits
    (gateLoopReady_of_coupled curveGatePlan _ _ attempts 1270 0 limit (limit + 3810) _ state ready
      (by omega) room attemptFits)
    (onlineNullSamples_tag attempts limit memory input coin state stored represented (nullSourceRoom limit room) attemptFits)

/-- Every accepted absent-output result retains the exact source and key buffers. -/
theorem onlineNullMemoryJoint_memory [FieldCertificate] (attempts limit : Nat)
    (memory : Memory) (input : AffineInput) (coin : OfflineCoin) (state : SharedOracleSource)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 3810) < 2 ^ 110)
    (result : OnlineJointMemoryResult)
    (supported : some result ∈ (onlineNullMemoryJoint attempts (sharedOfflineFrame coin) input memory state).support) :
    SharedSourceMemory result.2.1.1 result.2.2 (limit + 3810) ∧
      result.2.2.family.hash = state.family.hash ∧
      WordsAt result.2.1.1.ram (BitVec.ofNat 256 privateBase) 1 (inputKeySchedule.words coin.2.1) ∧
      result.2.1.1.ram (BitVec.ofNat 256 onlineInputBase) = BitVec.ofNat 256 input.x.val ∧
      result.2.1.1.ram (BitVec.ofNat 256 onlineInputBase + 1) = BitVec.ofNat 256 input.y.val := by
  obtain ⟨draw, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases draw with
  | none => simp at same
  | some draw =>
      have equal := Option.some.inj same
      subst result
      have ready := onlineNull_ready attempts limit memory input none [] coin state stored represented room
      have initial := onlineNullGateInitial_shared memory input none [] state limit represented (by omega)
      have preserved := gateLoopCoupled_memory curveGatePlan _ _ attempts 1270 0 limit _ state initial ready room draw member
      have ram : (onlineFinalMemory (onlineTagMemory draw.1.2.1)).ram = draw.1.2.1.ram := onlineFinalMemory_ram _
      have frame (cell : Nat) (lower : 32 ≤ cell) (upper : cell < 2 ^ 96) :
          (onlineFinalMemory (onlineTagMemory draw.1.2.1)).ram (BitVec.ofNat 256 cell) =
            (onlineCurveMemory memory input none []).ram (BitVec.ofNat 256 cell) := by
        rw [ram, preserved.2.2 cell lower upper]
        exact congrFun (onlineOriginalSetup_state (onlineTagMemory (onlineCurveMemory memory input none []))).1 _
      refine ⟨preserved.1.ramEq ram, preserved.2.1, ?_, ?_, ?_⟩
      · intro index inside
        have bound : index < 1016 := by simpa only [inputKeySchedule.wordsLength] using inside
        rw [← BitVec.ofNat_add, frame]
        · simpa only [BitVec.ofNat_add] using (onlineCurveMemory_keys memory input none [] coin stored) index inside
        · have fixed : 32 ≤ privateBase := by decide
          omega
        · have fixed : privateBase + 1017 < 2 ^ 96 := by decide
          omega
      · rw [frame onlineInputBase (by decide) (by decide)]
        exact (onlineCurveMemory_coordinates memory input none []).1
      · change (onlineFinalMemory (onlineTagMemory draw.1.2.1)).ram
          (BitVec.ofNat 256 onlineInputBase + BitVec.ofNat 256 1) = _
        rw [← BitVec.ofNat_add, frame (onlineInputBase + 1) (by decide) (by decide)]
        exact (onlineCurveMemory_coordinates memory input none []).2

end
end Kriterion.ArgoMAC.ArithmeticSimulator
