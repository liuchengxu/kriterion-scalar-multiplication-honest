import Proof.Privacy.Simulator.Arithmetic.CompiledProgramPrivate
import Proof.Privacy.Simulator.Arithmetic.CompiledBudget
import Proof.Privacy.Simulator.Arithmetic.SharedExactSourceGame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
open GarbledCircuit.SimulatorProtocol
noncomputable section
attribute [local irreducible] compiledQueryCoupledSamples offlineSchedule

/-- The chosen-input phase retains the complete offline source in private memory. -/
theorem compiledChosenProtocol [FieldCertificate] {Result : Type} {queries : Nat}
    (parameter : Nat) (state : State) (coin : SimulatorSampling.OfflineCoin)
    (setup : (state, coin) ∈ (compiledSetupJoint 256 parameter).support)
    (program : OracleProgram (publicOracleSpec Shared.FixedKeyIndex EncPRF.PermutationIndex) Result queries)
    (small : queries < 2 ^ 101) :
    let source := initialSharedOracleSource emptySharedMetadata
    let law := runSampledCutoff (fun request pair => compiledQueryCoupledSamples 256 pair.1 pair.2 request)
      program (state, source)
    law.map (Option.map fun result => (result.1, result.2.1)) =
      (runProgram (compiledMachine 256) program state).run ∧
    law.map (Option.map fun result => (result.1, result.2.2)) =
      runSampledCutoff (fun request => sharedSourceCutoff 256 (.inr request)) program source ∧
    ∀ value final, some (value, final) ∈ law.support →
      ∃ used, used ≤ queries ∧ CompiledPublicReady 256 0 0 0 state.spent used final.1 final.2 ∧
        WordsAt final.1.memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin) := by
  dsimp only
  let source := initialSharedOracleSource emptySharedMetadata
  have stored := compiledSetupJoint_memory 256 parameter state coin setup emptySharedMetadata rfl
  have cost := compiledSetupJoint_fixedCost parameter state coin setup
  have room : 256 + 2 * (0 + queries) < 2 ^ 110 := by
    have := oracleTable_capacity queries small
    omega
  have initial : CompiledPublicReady 256 0 0 0 state.spent 0 state source := by
    refine ⟨stored.1, ?_, stored.2.2.2, ?_⟩
    · rw [stored.2.2.1]
      exact Nat.le_refl 0
    · simp only [compiledPublicCost, Nat.zero_mul, Nat.add_zero, le_refl]
  have coupled := compiledProgram_coupling 256 0 0 0 state.spent queries room (by omega) (by decide)
    (fun used _ => compiledChosenCost_responseBudget state.spent used cost)
    program 0 state source (by omega) initial
  refine ⟨coupled.1, coupled.2.1, ?_⟩
  intro value final member
  obtain ⟨used, _, bound, ready⟩ := coupled.2.2 value final member
  refine ⟨used, by omega, ready, ?_⟩
  intro index inside
  have size : index < 838208 := by simpa only [offlineSchedule.wordsLength] using inside
  have lower : 51 ≤ privateBase + index := by unfold privateBase; omega
  have upper : privateBase + index < 2 ^ 96 := by unfold privateBase; omega
  have retained := compiledProgram_private 256 0 0 0 state.spent queries room (by omega) (by decide)
    program 0 state source (by omega) initial value final member (privateBase + index) lower upper
  have word := stored.2.1 index inside
  simpa only [Nat.zero_add, BitVec.ofNat_add] using retained.trans (by
    simpa only [Nat.zero_add, BitVec.ofNat_add] using word)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
