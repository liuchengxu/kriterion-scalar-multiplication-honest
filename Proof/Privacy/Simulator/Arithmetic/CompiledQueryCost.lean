import Proof.Privacy.Simulator.Arithmetic.CompiledQueryCounts
import Proof.Privacy.Simulator.Arithmetic.CompiledQueryMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine GarbledCircuit.SimulatorProtocol

/-- Each supported raw response fits the actual charged public-handler reserve. -/
theorem recordedPublicHandlerSamples_cost [BN254.FieldCertificate]
    (attempts count overlayCount : Nat) (memory : Memory) (request : SharedQuery) (rest : List Bool)
    (wire : memory.bits 0 = query request ++ rest)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256) (overlayFits : overlayCount < 2 ^ 256)
    (counts : PublicBranchCounts (publicHandlerKind request) attempts count overlayCount
      (recordedPublicInputMemory memory request rest))
    (result : Configuration 1810 × Nat)
    (supported : some result ∈ (recordedPublicHandlerSamples attempts count overlayCount memory request rest).support) :
    result.2 ≤ recordedPublicHandlerReserve attempts count overlayCount memory request rest := by
  have member : some result ∈ (run (recordedPublicHandler attempts)
      (recordedPublicHandlerReserve attempts count overlayCount memory request rest) ⟨0, memory⟩).support := by
    rw [recordedPublicHandler_run attempts count overlayCount memory request rest wire attemptFits tableFits overlayFits counts]
    exact supported
  exact run_cost (recordedPublicHandler attempts) _ _ result.1 result.2 member

/-- One compiled public query has a concrete linear reserve under the exact source count cap. -/
theorem compiledQueryReserve_bound (attempts limit : Nat) (state : State) (source : SharedOracleSource)
    (request : SharedQuery) (bounded : SharedSourceCounts source limit) (hashBound : source.family.hash.length ≤ limit) :
    2 + recordedPublicHandlerReserve attempts (publicSourceCount source request) (publicSourceOverlay source request)
      (compiledQueryMemory state.memory request) request [] ≤ 2574 * attempts + 44 * limit + 4449 := by
  have counts := publicSourceCounts_le source request limit bounded hashBound
  have cost := recordedPublicHandler_budget attempts (publicSourceCount source request) (publicSourceOverlay source request)
    (compiledQueryMemory state.memory request) request []
  change 1809 + 1 + _ ≤ _ at cost
  omega

/-- Every accepted coupled query retains the cumulative spent upper bound. -/
theorem compiledQueryCoupledSamples_cost [BN254.FieldCertificate]
    (attempts limit : Nat) (state : State) (source : SharedOracleSource) (request : SharedQuery)
    (represented : SharedSourceMemory state.memory source limit)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110)
    (hashBound : source.family.hash.length ≤ limit) (attemptFits : attempts < 2 ^ 256)
    (reply : SharedAnswer request) (final : State) (next : SharedOracleSource)
    (supported : some (reply, (final, next)) ∈ (compiledQueryCoupledSamples attempts state source request).support) :
    final.spent ≤ state.spent + (2574 * attempts + 44 * limit + 4449) := by
  obtain ⟨raw, member, answered, stateEq, sourceEq⟩ := compiledQueryCoupledSamples_support attempts state source request reply final next supported
  have limits := publicSourceCounts_le source request limit represented.counts hashBound
  have fits : limit < 2 ^ 256 := by omega
  have counts := recordedPublicInputMemory_counts attempts (compiledQueryMemory state.memory request) source request []
    represented.family represented.capacity (fun oracle => by have := represented.counts.1 oracle; omega)
  have cost := recordedPublicHandlerSamples_cost attempts (publicSourceCount source request) (publicSourceOverlay source request)
    (compiledQueryMemory state.memory request) request [] (by simp [compiledQueryMemory]) attemptFits
    (lt_of_le_of_lt limits.1 fits) (lt_of_le_of_lt limits.2 fits) counts raw member
  have reserve := compiledQueryReserve_bound attempts limit state source request represented.counts hashBound
  rw [stateEq]
  change state.spent + (raw.2 + 2) ≤ _
  omega

/-- The physical invariant and a numerical reserve supply the actual parsed-response marginal. -/
theorem compiledQueryCoupledSamples_physicalMachine [BN254.FieldCertificate]
    (attempts limit : Nat) (state : State) (source : SharedOracleSource) (request : SharedQuery)
    (represented : SharedSourceMemory state.memory source limit)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110)
    (hashBound : source.family.hash.length ≤ limit) (attemptFits : attempts < 2 ^ 256)
    (enough : state.spent + (2574 * attempts + 44 * limit + 4449) ≤ budget (state.queries + 1)) :
    (compiledQueryCoupledSamples attempts state source request).map (Option.map fun result => (result.1, result.2.1)) =
      parsedResponse (compiledMachine attempts) request state := by
  have limits := publicSourceCounts_le source request limit represented.counts hashBound
  have fits : limit < 2 ^ 256 := by omega
  have counts := recordedPublicInputMemory_counts attempts (compiledQueryMemory state.memory request) source request []
    represented.family represented.capacity (fun oracle => by have := represented.counts.1 oracle; omega)
  have reserve := compiledQueryReserve_bound attempts limit state source request represented.counts hashBound
  exact compiledQueryCoupledSamples_machine attempts state source request attemptFits
    (lt_of_le_of_lt limits.1 fits) (lt_of_le_of_lt limits.2 fits) counts (by omega)

end Kriterion.ArgoMAC.ArithmeticSimulator
