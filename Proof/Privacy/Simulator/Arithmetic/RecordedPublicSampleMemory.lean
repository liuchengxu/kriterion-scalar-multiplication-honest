import Proof.Privacy.Simulator.Arithmetic.RecordedPublicJoint

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine

/-- A supported forward handler result comes from its actual stored query sample. -/
theorem recordedPublicHandlerSamples_forwardMemory (attempts count overlayCount : Nat) (memory : Memory)
    (request : SharedQuery) (rest : List Bool) (kind : publicHandlerKind request = .forward)
    (result : Configuration 1810 × Nat)
    (supported : some result ∈ (recordedPublicHandlerSamples attempts count overlayCount memory request rest).support) :
    ∃ raw : Memory × Nat, raw ∈ (storedForwardSamples attempts count (recordedPublicInputMemory memory request rest)).support ∧
      result.1.memory = (recordedPublicForwardTail overlayCount raw.1).1 := by
  simp only [recordedPublicHandlerSamples, kind, recordedPublicBranchSamples, PMF.map_comp] at supported
  obtain ⟨raw, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  refine ⟨raw, member, ?_⟩
  have equal := Option.some.inj same
  exact (congrArg (fun final : Configuration 1810 × Nat => final.1.memory) equal).symm

/-- A supported inverse handler result comes from its actual stored query sample. -/
theorem recordedPublicHandlerSamples_inverseMemory (attempts count overlayCount : Nat) (memory : Memory)
    (request : SharedQuery) (rest : List Bool) (kind : publicHandlerKind request = .inverse)
    (result : Configuration 1810 × Nat)
    (supported : some result ∈ (recordedPublicHandlerSamples attempts count overlayCount memory request rest).support) :
    ∃ raw : Memory × Nat, raw ∈ (storedInverseSamples attempts count
      (publicInversePrepared overlayCount (recordedPublicInputMemory memory request rest))).support ∧
      result.1.memory = (recordedPublicInverseTail raw.1).1 := by
  simp only [recordedPublicHandlerSamples, kind, recordedPublicBranchSamples, PMF.map_comp] at supported
  obtain ⟨raw, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  refine ⟨raw, member, ?_⟩
  have equal := Option.some.inj same
  exact (congrArg (fun final : Configuration 1810 × Nat => final.1.memory) equal).symm

/-- A supported hash handler result comes from its actual hash query sample. -/
theorem recordedPublicHandlerSamples_hashMemory (attempts count overlayCount : Nat) (memory : Memory)
    (request : SharedQuery) (rest : List Bool) (kind : publicHandlerKind request = .hash)
    (result : Configuration 1810 × Nat)
    (supported : some result ∈ (recordedPublicHandlerSamples attempts count overlayCount memory request rest).support) :
    ∃ raw : Memory × Nat, raw ∈ (hashHandlerSamples count (recordedPublicInputMemory memory request rest)).support ∧
      result.1.memory = (recordedPublicHashTail raw.1).1 := by
  simp only [recordedPublicHandlerSamples, kind, recordedPublicBranchSamples, PMF.map_comp] at supported
  obtain ⟨raw, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  refine ⟨raw, member, ?_⟩
  have equal := Option.some.inj same
  exact (congrArg (fun final : Configuration 1810 × Nat => final.1.memory) equal).symm

end Kriterion.ArgoMAC.ArithmeticSimulator
