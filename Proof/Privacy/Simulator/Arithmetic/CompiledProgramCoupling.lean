import Proof.Privacy.Simulator.Arithmetic.ParsedProgramBounded
import Proof.Privacy.Simulator.Arithmetic.CompiledQueryCost

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine GarbledCircuit.SimulatorProtocol
noncomputable section

/-- This allowance bounds the cumulative cost of the public calls. -/
def compiledPublicCost (attempts base used : Nat) : Nat :=
  used * (2574 * attempts + 44 * (base + used) + 4449)

/-- The next allowance pays for one query at the current source count cap. -/
theorem compiledPublicCost_step (attempts base used : Nat) :
    compiledPublicCost attempts base used + (2574 * attempts + 44 * (base + used) + 4449) ≤
      compiledPublicCost attempts base (used + 1) := by
  unfold compiledPublicCost
  nlinarith

/-- The public phase retains the physical source, both counters, and its cost allowance. -/
structure CompiledPublicReady (attempts base hashBase initialQueries initialSpent used : Nat)
    (state : State) (source : SharedOracleSource) : Prop where
  memory : SharedSourceMemory state.memory source (base + used)
  hash : source.family.hash.length ≤ hashBase + used
  queries : state.queries = initialQueries + used
  spent : state.spent ≤ initialSpent + compiledPublicCost attempts base used

/-- Each accepted query advances the indexed public-phase relation. -/
theorem compiledPublicReady_step [BN254.FieldCertificate]
    (attempts base hashBase initialQueries initialSpent total used : Nat)
    (state : State) (source : SharedOracleSource) (request : SharedQuery)
    (initial : CompiledPublicReady attempts base hashBase initialQueries initialSpent used state source)
    (available : used < total) (room : 256 + 2 * (base + total) < 2 ^ 110)
    (hashBaseBound : hashBase ≤ base) (attemptFits : attempts < 2 ^ 256)
    (reply : SharedAnswer request) (final : State) (next : SharedOracleSource)
    (supported : some (reply, (final, next)) ∈ (compiledQueryCoupledSamples attempts state source request).support) :
    CompiledPublicReady attempts base hashBase initialQueries initialSpent (used + 1) final next := by
  have stepRoom : 256 + 2 * (base + used + 1) < 2 ^ 110 := by omega
  have hashBound : source.family.hash.length ≤ base + used := by have := initial.hash; omega
  have stored := compiledQueryCoupledSamples_memory attempts (base + used) state source request initial.memory
    stepRoom (by omega) reply final next supported
  have cost := compiledQueryCoupledSamples_cost attempts (base + used) state source request initial.memory
    stepRoom hashBound attemptFits reply final next supported
  have advance := compiledPublicCost_step attempts base used
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using stored.1
  · have := initial.hash; omega
  · have := initial.queries; omega
  · have := initial.spent; omega

/-- The public program has the exact machine and cutoff-source marginals within its query budget. -/
theorem compiledProgram_coupling [BN254.FieldCertificate] {Result : Type}
    (attempts base hashBase initialQueries initialSpent total : Nat)
    (room : 256 + 2 * (base + total) < 2 ^ 110)
    (hashBaseBound : hashBase ≤ base) (attemptFits : attempts < 2 ^ 256)
    (enough : ∀ used, used < total →
      initialSpent + compiledPublicCost attempts base (used + 1) ≤ budget (initialQueries + used + 1))
    {remaining : Nat} (program : OracleProgram (publicOracleSpec Shared.FixedKeyIndex EncPRF.PermutationIndex) Result remaining)
    (used : Nat) (state : State) (source : SharedOracleSource) (available : used + remaining ≤ total)
    (initial : CompiledPublicReady attempts base hashBase initialQueries initialSpent used state source) :
    let law := runSampledCutoff (fun request pair => compiledQueryCoupledSamples attempts pair.1 pair.2 request)
      program (state, source)
    law.map (Option.map fun result => (result.1, result.2.1)) =
      (runProgram (compiledMachine attempts) program state).run ∧
    law.map (Option.map fun result => (result.1, result.2.2)) =
      runSampledCutoff (fun request => sharedSourceCutoff attempts (.inr request)) program source ∧
    ∀ value final, some (value, final) ∈ law.support →
      ∃ finalUsed, used ≤ finalUsed ∧ finalUsed ≤ used + remaining ∧
        CompiledPublicReady attempts base hashBase initialQueries initialSpent finalUsed final.1 final.2 := by
  apply runProgram_boundedCoupling (compiledMachine attempts)
    (fun request => sharedSourceCutoff attempts (.inr request))
    (fun request pair => compiledQueryCoupledSamples attempts pair.1 pair.2 request) total
    (CompiledPublicReady attempts base hashBase initialQueries initialSpent)
    (program := program) (used := used) (state := state) (initialSource := source)
  · intro used request pair available ready
    have stepRoom : 256 + 2 * (base + used + 1) < 2 ^ 110 := by omega
    apply compiledQueryCoupledSamples_physicalMachine attempts (base + used) pair.1 pair.2 request
      ready.memory stepRoom (by have := ready.hash; omega) attemptFits
    have cost := compiledPublicCost_step attempts base used
    have fits := enough used available
    rw [ready.queries]
    calc
      _ ≤ (initialSpent + compiledPublicCost attempts base used) +
          (2574 * attempts + 44 * (base + used) + 4449) := Nat.add_le_add_right ready.spent _
      _ = initialSpent + (compiledPublicCost attempts base used +
          (2574 * attempts + 44 * (base + used) + 4449)) := Nat.add_assoc _ _ _
      _ ≤ initialSpent + compiledPublicCost attempts base (used + 1) := Nat.add_le_add_left cost _
      _ ≤ _ := fits
  · intro used request pair available ready
    exact compiledQueryCoupledSamples_source attempts pair.1 pair.2 request ready.memory.family
      ready.memory.capacity ready.memory.history
      (fun oracle => by have := ready.memory.counts.1 oracle; omega)
      (fun index => by have := ready.memory.counts.2.2 index; omega)
  · intro used request pair available ready reply final supported
    exact compiledPublicReady_step attempts base hashBase initialQueries initialSpent total used
      pair.1 pair.2 request ready available room hashBaseBound attemptFits reply final.1 final.2 supported
  · exact available
  · exact initial

end
end Kriterion.ArgoMAC.ArithmeticSimulator
