import Proof.Privacy.Simulator.Arithmetic.OnlineValidConcrete

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorSampling Security.SharedSimulatorMachine
noncomputable section

private theorem curveRoom (limit : Nat) (room : 256 + 2 * (limit + 836422) < 2 ^ 110) :
    256 + 2 * (limit + 3810) < 2 ^ 110 := by
  ring_nf at room ⊢
  omega

/-- Both actual online branches have the exact finite shared source law. -/
theorem onlineMemoryJoint_concreteSource [FieldCertificate] [GroupCertificate]
    (attempts limit : Nat) (memory : Memory) (input : AffineInput) (output : Option Point)
    (coin : OfflineCoin) (state : SharedOracleSource)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 836422) < 2 ^ 110)
    (hashRoom : 2 * (state.family.hash.length + 1) + 256 < 2 ^ 110) :
    (onlineMemoryJoint attempts coin input output memory state).map
      (Option.map fun result => (result.1, result.2.2)) =
      runSampledCutoff (sharedSourceCutoff attempts)
        (sharedOnlineTotalProgram attempts (sharedOfflineFrame coin) input output) state := by
  cases output with
  | none =>
      exact onlineNullMemoryJoint_source attempts limit (sharedOfflineFrame coin) input memory state
        (onlineNull_ready attempts limit memory input none [] coin state stored represented (curveRoom limit room))
        (curveRoom limit room)
  | some output =>
      exact onlineValidMemoryJoint_concreteSource attempts limit memory input output coin state stored represented room hashRoom

/-- The complete online protocol joint has the exact finite shared source marginal. -/
theorem compiledOnlineJoint_concreteSource [FieldCertificate] [GroupCertificate]
    (attempts limit : Nat) (coin : OfflineCoin) (input : AffineInput) (output : Option Point)
    (state : State) (source : SharedOracleSource)
    (stored : WordsAt state.memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (represented : SharedSourceMemory state.memory source limit)
    (room : 256 + 2 * (limit + 836422) < 2 ^ 110)
    (hashRoom : 2 * (source.family.hash.length + 1) + 256 < 2 ^ 110) :
    (compiledOnlineJoint attempts coin input output state source).map
      (Option.map fun result => (result.1, result.2.2)) =
      runSampledCutoff (sharedSourceCutoff attempts)
        (sharedOnlineTotalProgram attempts (sharedOfflineFrame coin) input output) source := by
  simp only [compiledOnlineJoint, PMF.map_comp, Option.map_map, Function.comp_def]
  exact onlineMemoryJoint_concreteSource attempts limit _ input output coin source stored
    (represented.ramEq rfl) room hashRoom

end
end Kriterion.ArgoMAC.ArithmeticSimulator
