import Proof.Privacy.Simulator.Arithmetic.CompiledChosenProtocol

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
open GarbledCircuit.SimulatorProtocol
noncomputable section
attribute [local irreducible] compiledQueryCoupledSamples

/-- The accepted online state supplies the complete reserve for all decision queries. -/
structure CompiledDecisionReady (chosen : Nat) (state : State) (source : SharedOracleSource) : Prop where
  memory : SharedSourceMemory state.memory source (chosen + 836423)
  hash : source.family.hash.length ≤ chosen + 1
  queries : state.queries = chosen
  spent : state.spent ≤ compiledBlockAllowance chosen

/-- The final adaptive phase has exact actual-machine and finite-source marginals. -/
theorem compiledDecisionProtocol [FieldCertificate] {Result : Type} {queries : Nat}
    (chosen : Nat) (state : State) (source : SharedOracleSource)
    (ready : CompiledDecisionReady chosen state source)
    (program : OracleProgram (publicOracleSpec Shared.FixedKeyIndex EncPRF.PermutationIndex) Result queries)
    (small : chosen + queries < 2 ^ 101) :
    let law := runSampledCutoff (fun request pair => compiledQueryCoupledSamples 256 pair.1 pair.2 request)
      program (state, source)
    law.map (Option.map fun result => (result.1, result.2.1)) =
      (runProgram (compiledMachine 256) program state).run ∧
    law.map (Option.map fun result => (result.1, result.2.2)) =
      runSampledCutoff (fun request => sharedSourceCutoff 256 (.inr request)) program source ∧
    ∀ value final, some (value, final) ∈ law.support →
      ∃ used, used ≤ queries ∧
        CompiledPublicReady 256 (chosen + 836423) (chosen + 1) chosen state.spent used final.1 final.2 := by
  dsimp only
  have room : 256 + 2 * ((chosen + 836423) + queries) < 2 ^ 110 := by
    have := compiledPublicCost_room chosen queries small
    omega
  have initial : CompiledPublicReady 256 (chosen + 836423) (chosen + 1) chosen state.spent 0 state source := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [Nat.add_zero] using ready.memory
    · simpa only [Nat.add_zero] using ready.hash
    · simpa only [Nat.add_zero] using ready.queries
    · simp only [compiledPublicCost, Nat.zero_mul, Nat.add_zero, le_refl]
  have coupled := compiledProgram_coupling 256 (chosen + 836423) (chosen + 1) chosen state.spent queries
    room (by omega) (by decide) (fun used _ => compiledDecisionCost_responseBudget chosen state.spent used ready.spent)
    program 0 state source (by omega) initial
  refine ⟨coupled.1, coupled.2.1, ?_⟩
  intro value final supported
  obtain ⟨used, _, bounded, preserved⟩ := coupled.2.2 value final supported
  exact ⟨used, by omega, preserved⟩

end
end Kriterion.ArgoMAC.ArithmeticSimulator
