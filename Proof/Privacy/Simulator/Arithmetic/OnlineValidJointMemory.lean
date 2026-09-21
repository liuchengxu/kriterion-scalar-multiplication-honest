import Proof.Privacy.Simulator.Arithmetic.OnlineLinkedGateReady
import Proof.Privacy.Simulator.Arithmetic.OnlineValidGateParser

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorSampling Security.SharedSimulatorMachine
noncomputable section
set_option maxRecDepth 2048
attribute [local irreducible] onlineSamplingMemory onlineSamplingCoin onlinePreparedMemory encLinkSamples
attribute [local irreducible] onlineValidGateJoint onlineCurveJoint onlinePointJoint gateLoopCoupled

/-- Every accepted valid joint retains the shared source and emits the exact selected labels. -/
theorem onlineValidMemoryJoint_memory [FieldCertificate] [GroupCertificate]
    (attempts limit : Nat) (memory : Memory) (input : AffineInput) (output : Point)
    (coin : OfflineCoin) (state : SharedOracleSource)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 836423) < 2 ^ 110)
    (hashRoom : 2 * (state.family.hash.length + 1) + 256 < 2 ^ 110)
    (attemptFits : attempts < 2 ^ 256) (empty : memory.bits 3 = [])
    (result : OnlineJointMemoryResult)
    (supported : some result ∈ (onlineValidMemoryJoint attempts (sharedOfflineFrame coin)
      input output coin.2.2 memory state).support) :
    SharedSourceMemory result.2.1.1 result.2.2 (limit + 836422) ∧
      GarbledCircuit.SimulatorProtocol.words 128 508 (result.2.1.1.bits 3) =
        some (Lamport.selectedLabels result.1.inputMac) := by
  unfold onlineValidMemoryJoint at supported
  obtain ⟨sampled, sampleMember, linkMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨linked, linkedSupport, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp linkMember
  by_cases accepted : linked.1.2.2 = 7466
  · simp only [if_pos accepted] at member
    obtain ⟨raw, gateMember, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    cases raw with
    | none => simp at same
    | some final =>
      have same := Option.some.inj same
      subst result
      let base := onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))
      let sample := onlineSamplingCoin attempts base sampled
      let prepared := onlinePreparedMemory sampled.1 output sample
      have linkRoom : 2 * (limit + 508) + 256 < 2 ^ 110 := by ring_nf at room ⊢; omega
      have gateRoom : 256 + 2 * (limit + 508 + 3 * 278638) < 2 ^ 110 := by ring_nf at room ⊢; omega
      have curveRoom : 256 + 2 * (limit + 508 + 3810) < 2 ^ 110 := by ring_nf at room ⊢; omega
      have ready := onlineValidLink_ready attempts limit memory input output coin state stored represented
        (by ring_nf at room ⊢; omega) sampled sampleMember
      have data := onlineValidLinked_gateMemory attempts limit memory input output coin state stored sampled sampleMember
        ready linkRoom hashRoom linked linkedSupport accepted
      have retained := onlineValidGateJoint_memory attempts (limit + 508) (sharedOfflineFrame coin) input
        ((sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2)
        (encLinkOutputMac linked.1.1 onlineLinkedBase) linked.1.1 {state with family := linked.2}
        data.represented (data.curveReady attempts curveRoom) (data.pointReady attempts gateRoom) gateRoom attemptFits final gateMember
      refine ⟨?_, ?_⟩
      · have source := retained.1
        have cap : limit + 508 + 835914 = limit + 836422 := by omega
        rw [cap] at source
        exact source
      · have pointer : base.registers 10 = BitVec.ofNat 256 onlineSampleBase := rfl
        have keys := onlinePreparedMemory_keys attempts base sampled.1 sampled.2 pointer sampleMember output sample coin.2.1
          (onlineCurveMemory_keys memory input (some output) [] coin stored)
        have linkedKeys : WordsAt linked.1.1.ram (BitVec.ofNat 256 privateBase) 1 (inputKeySchedule.words coin.2.1) := by
          intro index inside
          have bound : index < 1016 := by simpa only [inputKeySchedule.wordsLength] using inside
          rw [← BitVec.ofNat_add, encLinkSamples_beforeOutput attempts limit onlineLinkedBase
            (privateBase + (1 + index)) prepared state.family coin.2.2 [] ready.represented.family ready.represented.capacity
            ready.operand ready.outputPointer (by decide) (by decide) ready.represented.counts.1 ready.represented.counts.2.1
            linkRoom hashRoom ready.wire (by unfold privateBase; omega)
            (by unfold onlineLinkedBase; omega) linked linkedSupport]
          simpa only [BitVec.ofNat_add] using keys index inside
        have linkedEmpty : linked.1.1.bits 3 = [] := by
          rw [encLinkSamples_bits3 attempts prepared state.family coin.2.2 [] linked linkedSupport]
          rw [onlinePreparedMemory_bits, onlineSamplingMemory_bits attempts base sampled.1 sampled.2 sampleMember]
          change (onlineCurveMemory memory input (some output) []).bits 3 = []
          rw [onlineCurveMemory_bits]
          exact empty
        exact onlineValidGateJoint_keyProtocol attempts (limit + 508) (sharedOfflineFrame coin) input _ _ _ _
          data.represented (data.curveReady attempts curveRoom) (data.pointReady attempts gateRoom) gateRoom attemptFits
          coin.2.1 (sharedOfflineFrame_inputMac coin input) linkedKeys data.coordinates linkedEmpty final gateMember
  · simp only [if_neg accepted, PMF.mem_support_pure_iff] at member
    cases member

end
end Kriterion.ArgoMAC.ArithmeticSimulator
