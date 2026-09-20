import Proof.Privacy.Simulator.Arithmetic.RecordedPublicCallerSource
import Proof.Privacy.Simulator.Arithmetic.CompiledProgramCoupling

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine
noncomputable section
attribute [local irreducible] compiledQueryCoupledSamples
set_option maxHeartbeats 400000

/-- An accepted coupled query retains every caller buffer word. -/
theorem compiledQueryCoupledSamples_private [BN254.FieldCertificate]
    (attempts limit : Nat) (state : State) (source : SharedOracleSource) (request : SharedQuery)
    (represented : SharedSourceMemory state.memory source limit)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) (hashBound : source.family.hash.length ≤ limit)
    (reply : SharedAnswer request) (final : State) (next : SharedOracleSource)
    (supported : some (reply, (final, next)) ∈ (compiledQueryCoupledSamples attempts state source request).support)
    (cell : Nat) (lower : 51 ≤ cell) (upper : cell < 2 ^ 96) :
    final.memory.ram (BitVec.ofNat 256 cell) = state.memory.ram (BitVec.ofNat 256 cell) := by
  obtain ⟨raw, member, _, same, _⟩ := compiledQueryCoupledSamples_support attempts state source request reply final next supported
  rw [same]
  exact recordedPublicHandlerSamples_private attempts limit (compiledQueryMemory state.memory request)
    source request [] ⟨represented.family, represented.capacity, represented.history, represented.counts⟩
    room hashBound raw member cell lower upper

/-- A complete adaptive public phase retains every private buffer word at its actual query count. -/
theorem compiledProgram_private [BN254.FieldCertificate] {Result : Type}
    (attempts base hashBase initialQueries initialSpent total : Nat)
    (room : 256 + 2 * (base + total) < 2 ^ 110)
    (hashBaseBound : hashBase ≤ base) (attemptFits : attempts < 2 ^ 256)
    {remaining : Nat} (program : OracleProgram (publicOracleSpec Shared.FixedKeyIndex EncPRF.PermutationIndex) Result remaining)
    (used : Nat) (state : State) (source : SharedOracleSource) (available : used + remaining ≤ total)
    (initial : CompiledPublicReady attempts base hashBase initialQueries initialSpent used state source)
    (value : Result) (final : State × SharedOracleSource)
    (member : some (value, final) ∈
      (runSampledCutoff (fun request pair => compiledQueryCoupledSamples attempts pair.1 pair.2 request)
        program (state, source)).support)
    (cell : Nat) (lower : 51 ≤ cell) (upper : cell < 2 ^ 96) :
    final.1.memory.ram (BitVec.ofNat 256 cell) = state.memory.ram (BitVec.ofNat 256 cell) := by
  let related (used : Nat) (pair : State × SharedOracleSource) : Prop :=
    CompiledPublicReady attempts base hashBase initialQueries initialSpent used pair.1 pair.2 ∧
      pair.1.memory.ram (BitVec.ofNat 256 cell) = state.memory.ram (BitVec.ofNat 256 cell)
  have preserved : ∀ (used : Nat) (request : SharedQuery) (pair : State × SharedOracleSource),
      used < total → related used pair → ∀ (reply : SharedAnswer request) (next : State × SharedOracleSource),
      some (reply, next) ∈ (compiledQueryCoupledSamples attempts pair.1 pair.2 request).support → related (used + 1) next := by
    intro used request pair available ready reply next supported
    refine ⟨compiledPublicReady_step attempts base hashBase initialQueries initialSpent total used
      pair.1 pair.2 request ready.1 available room hashBaseBound attemptFits reply next.1 next.2 supported, ?_⟩
    exact (compiledQueryCoupledSamples_private attempts (base + used) pair.1 pair.2 request ready.1.memory
      (by omega) (by have := ready.1.hash; omega) reply next.1 next.2 supported cell lower upper).trans ready.2
  obtain ⟨_, _, _, retained⟩ := runSampledCutoff_boundedReady
    (oracle := publicOracleSpec Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (fun request pair => compiledQueryCoupledSamples attempts pair.1 pair.2 request) total related preserved
    program used (state, source) available ⟨initial, rfl⟩ value final member
  exact retained.2

end
end Kriterion.ArgoMAC.ArithmeticSimulator
