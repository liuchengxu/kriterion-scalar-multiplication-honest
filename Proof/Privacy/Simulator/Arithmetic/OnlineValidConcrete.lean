import Proof.Privacy.Simulator.Arithmetic.OnlineLinkedGateReady
import Proof.Privacy.Simulator.Arithmetic.OnlineValidJointMachine
import Proof.Privacy.Simulator.Arithmetic.OnlineValidJointSource
import Proof.Privacy.Simulator.Arithmetic.OnlineLinkSharedSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorSampling Security.SharedSimulatorMachine
noncomputable section

private theorem validGateRoom (limit : Nat) (room : 256 + 2 * (limit + 836422) < 2 ^ 110) :
    256 + 2 * (limit + 508 + 3 * 278638) < 2 ^ 110 := by
  ring_nf at room ⊢
  exact room

private theorem validCurveRoom (limit : Nat) (room : 256 + 2 * (limit + 836422) < 2 ^ 110) :
    256 + 2 * (limit + 508 + 3810) < 2 ^ 110 := by
  ring_nf at room ⊢
  omega

private theorem validLinkRoom (limit : Nat) (room : 256 + 2 * (limit + 836422) < 2 ^ 110) :
    2 * (limit + 508) + 256 < 2 ^ 110 := by
  ring_nf at room ⊢
  omega

private theorem validInitialRoom (limit : Nat) (room : 256 + 2 * (limit + 836422) < 2 ^ 110) :
    256 + 2 * (limit + 1) < 2 ^ 110 := by
  ring_nf at room ⊢
  omega

/-- The complete actual valid joint has the exact accepted online machine marginal. -/
theorem onlineValidMemoryJoint_concreteMachine [FieldCertificate] [GroupCertificate]
    (attempts limit : Nat) (memory : Memory) (input : AffineInput) (output : Point)
    (coin : OfflineCoin) (state : SharedOracleSource)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 836422) < 2 ^ 110)
    (hashRoom : 2 * (state.family.hash.length + 1) + 256 < 2 ^ 110)
    (attemptFits : attempts < 2 ^ 256) :
    (onlineValidMemoryJoint attempts (sharedOfflineFrame coin) input output coin.2.2 memory state).map
      (Option.map fun result => result.2.1) =
      (onlineValidSamples attempts memory input output state.family coin.2.2 []).map
        (fun result => if result.1.pc = 290305298 then some (result.1.memory, result.2) else none) := by
  apply onlineValidMemoryJoint_machine
  intro sampled supported
  dsimp only
  intro linked linkedSupport accepted
  have linkReady := onlineValidLink_ready attempts limit memory input output coin state stored represented
    (validInitialRoom limit room) sampled supported
  have ready := onlineValidLinked_gateMemory attempts limit memory input output coin state stored sampled supported
    linkReady (validLinkRoom limit room) hashRoom linked linkedSupport accepted
  exact onlineValidGateJoint_machine attempts (limit + 508) _ _ _ _ _ _
    (ready.curveReady attempts (validCurveRoom limit room))
    (ready.pointReady attempts (validGateRoom limit room)) (validGateRoom limit room) attemptFits

/-- The complete actual valid joint has the exact finite online source marginal. -/
theorem onlineValidMemoryJoint_concreteSource [FieldCertificate] [GroupCertificate]
    (attempts limit : Nat) (memory : Memory) (input : AffineInput) (output : Point)
    (coin : OfflineCoin) (state : SharedOracleSource)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 836422) < 2 ^ 110)
    (hashRoom : 2 * (state.family.hash.length + 1) + 256 < 2 ^ 110) :
    (onlineValidMemoryJoint attempts (sharedOfflineFrame coin) input output coin.2.2 memory state).map
      (Option.map fun result => (result.1, result.2.2)) =
      runSampledCutoff (sharedSourceCutoff attempts)
        (sharedOnlineTotalProgram attempts (sharedOfflineFrame coin) input (some output)) state := by
  apply onlineValidMemoryJoint_source
  · intro sampled supported
    have ready := onlineValidLink_ready attempts limit memory input output coin state stored represented
      (validInitialRoom limit room) sampled supported
    exact onlineLinkMemory_sharedSource attempts limit _ state coin input ready (validLinkRoom limit room) hashRoom
  · intro sampled supported
    dsimp only
    intro linked linkedSupport accepted
    have linkReady := onlineValidLink_ready attempts limit memory input output coin state stored represented
      (validInitialRoom limit room) sampled supported
    have ready := onlineValidLinked_gateMemory attempts limit memory input output coin state stored sampled supported
      linkReady (validLinkRoom limit room) hashRoom linked linkedSupport accepted
    exact onlineValidGateJoint_source attempts (limit + 508) _ _ _ _ _ _
      (ready.curveReady attempts (validCurveRoom limit room))
      (ready.pointReady attempts (validGateRoom limit room)) (validGateRoom limit room)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
