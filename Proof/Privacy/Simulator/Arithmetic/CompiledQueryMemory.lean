import Proof.Privacy.Simulator.Arithmetic.CompiledQueryCoupling
import Proof.Privacy.Simulator.Arithmetic.SharedPublicGrowth

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine GarbledCircuit.SimulatorProtocol

/-- An accepted protocol query preserves the complete physical source and advances both count caps. -/
theorem compiledQueryCoupledSamples_memory [BN254.FieldCertificate]
    (attempts limit : Nat) (state : State) (source : SharedOracleSource) (request : SharedQuery)
    (represented : SharedSourceMemory state.memory source limit)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110)
    (hashRoom : 2 * (source.family.hash.length + 1) + 256 < 2 ^ 110)
    (reply : SharedAnswer request) (final : State) (next : SharedOracleSource)
    (supported : some (reply, (final, next)) ∈ (compiledQueryCoupledSamples attempts state source request).support) :
    SharedSourceMemory final.memory next (limit + 1) ∧
      next.family.hash.length ≤ source.family.hash.length + 1 ∧ final.queries = state.queries + 1 ∧
      state.spent + 2 ≤ final.spent := by
  obtain ⟨raw, member, answered, stateEq, sourceEq⟩ := compiledQueryCoupledSamples_support attempts state source request reply final next supported
  subst final
  subst next
  have joint : (some raw, some (reply, sharedPublicNext source request reply)) ∈
      (recordedPublicJoint attempts (compiledQueryMemory state.memory request) source request []).support := by
    apply (PMF.mem_support_map_iff _ _ _).mpr
    refine ⟨some raw, member, ?_⟩
    simp only [Option.bind_some, answered, Option.map_some]
  have stored := recordedPublicJoint_memory attempts (compiledQueryMemory state.memory request) source request []
    represented.family represented.capacity represented.history
    (fun oracle => by have := represented.counts.1 oracle; omega) hashRoom
    (fun index => by have := represented.counts.2.2 index; omega) (by simp [compiledQueryMemory]) raw reply _ joint
  refine ⟨⟨stored.1, stored.2.1, stored.2.2, sharedPublicNext_counts source request reply limit represented.counts⟩,
    sharedPublicNext_hashLength source request reply, rfl, ?_⟩
  change state.spent + 2 ≤ state.spent + (raw.2 + 2)
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
