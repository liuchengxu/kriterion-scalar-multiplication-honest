import Proof.Privacy.Simulator.Arithmetic.CompiledQueryProtocol
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicJointMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine GarbledCircuit.SimulatorProtocol
noncomputable section

/-- A public result retains its actual memory and both cumulative counters. -/
def compiledQueryNext (state : State) (result : Configuration 1810 × Nat) : State :=
  ⟨result.1.memory, state.spent + (result.2 + 2), state.queries + 1⟩

/-- The coupled response retains the typed reply, charged machine state, and complete source state. -/
def compiledQueryCoupledSamples (attempts : Nat) (state : State) (source : SharedOracleSource) (request : SharedQuery) :
    PMF (Option (SharedAnswer request × (State × SharedOracleSource))) :=
  (recordedPublicHandlerSamples attempts (publicSourceCount source request) (publicSourceOverlay source request)
    (compiledQueryMemory state.memory request) request []).map fun result =>
      result.bind fun result => (answer request (result.1.memory.bits 3)).map fun reply =>
        (reply, (compiledQueryNext state result, sharedPublicNext source request reply))

/-- The first coupled marginal is the actual parsed protocol response with its exact charge. -/
theorem compiledQueryCoupledSamples_machine [BN254.FieldCertificate]
    (attempts : Nat) (state : State) (source : SharedOracleSource) (request : SharedQuery)
    (attemptFits : attempts < 2 ^ 256)
    (tableFits : publicSourceCount source request < 2 ^ 256)
    (overlayFits : publicSourceOverlay source request < 2 ^ 256)
    (counts : PublicBranchCounts (publicHandlerKind request) attempts (publicSourceCount source request)
      (publicSourceOverlay source request) (recordedPublicInputMemory (compiledQueryMemory state.memory request) request []))
    (enough : state.spent + (2 + recordedPublicHandlerReserve attempts (publicSourceCount source request)
      (publicSourceOverlay source request) (compiledQueryMemory state.memory request) request []) ≤ budget (state.queries + 1)) :
    (compiledQueryCoupledSamples attempts state source request).map (Option.map fun result => (result.1, result.2.1)) =
      parsedResponse (compiledMachine attempts) request state := by
  rw [compiledMachine_parsedResponse attempts _ _ state request attemptFits tableFits overlayFits counts enough]
  simp only [compiledQueryCoupledSamples, PMF.map_comp, Function.comp_def]
  apply publicReply_map
  intro result supported
  cases result with
  | none => rfl
  | some result =>
      simp only [Option.bind_some, Option.map_map, Function.comp_def, compiledQueryNext]

/-- The second coupled marginal is the exact shared public cutoff source. -/
theorem compiledQueryCoupledSamples_source [BN254.FieldCertificate]
    (attempts : Nat) (state : State) (source : SharedOracleSource) (request : SharedQuery)
    (represented : OracleFamilyMemory state.memory.ram source.family) (capacity : OracleFamilyFits source.family)
    (history : SharedHistoryMemory state.memory.ram source.metadata)
    (room : ∀ oracle, 2 * ((source.family.permutations oracle).base.used + 1) ≤ 2 ^ 110)
    (historyRoom : ∀ index, 257 + 2 * (recordHistoryPairs source.metadata.fixedTranscript index).length < 2 ^ 110) :
    (compiledQueryCoupledSamples attempts state source request).map (Option.map fun result => (result.1, result.2.2)) =
      sharedSourceCutoff attempts (.inr request) source := by
  have law := recordedPublicJoint_physicalSource attempts (compiledQueryMemory state.memory request) source request []
    represented capacity history room historyRoom (by simp [compiledQueryMemory])
  rw [← law]
  simp only [compiledQueryCoupledSamples, recordedPublicJoint, PMF.map_comp, Function.comp_def]
  apply publicReply_map
  intro result supported
  cases result with
  | none => rfl
  | some result =>
      simp only [Option.bind_some, Option.map_map, Function.comp_def, compiledQueryNext]

/-- Every accepted coupled result has the exact raw query sample and parsed reply. -/
theorem compiledQueryCoupledSamples_support (attempts : Nat) (state : State) (source : SharedOracleSource)
    (request : SharedQuery) (reply : SharedAnswer request) (final : State) (next : SharedOracleSource)
    (supported : some (reply, (final, next)) ∈ (compiledQueryCoupledSamples attempts state source request).support) :
    ∃ raw : Configuration 1810 × Nat,
      some raw ∈ (recordedPublicHandlerSamples attempts (publicSourceCount source request) (publicSourceOverlay source request)
        (compiledQueryMemory state.memory request) request []).support ∧
      answer request (raw.1.memory.bits 3) = some reply ∧
      final = compiledQueryNext state raw ∧ next = sharedPublicNext source request reply := by
  obtain ⟨raw, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases raw with
  | none => simp at same
  | some raw =>
      change (answer request (raw.1.memory.bits 3)).map _ = _ at same
      cases decoded : answer request (raw.1.memory.bits 3) with
      | none => simp only [decoded, Option.map_none] at same; contradiction
      | some value =>
          rw [decoded, Option.map_some] at same
          obtain ⟨rfl, equal⟩ := Prod.mk.inj (Option.some.inj same)
          have states := Prod.mk.inj equal
          exact ⟨raw, member, decoded, states.1.symm, states.2.symm⟩

end
end Kriterion.ArgoMAC.ArithmeticSimulator
