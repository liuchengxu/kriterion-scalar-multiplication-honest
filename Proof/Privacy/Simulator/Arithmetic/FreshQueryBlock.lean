import Proof.Privacy.Simulator.Arithmetic.FreshQuery
import Proof.Privacy.Simulator.Arithmetic.ByteOutputBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A host contains the fresh-query path before its return instruction. -/
def ContainsFreshQuery (host : Machine) (attempts : Nat)
    (labels : Fin 115 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 115, pc ≠ 114 → host.code[(labels pc).val] =
    relocate labels ((freshQuery attempts).code[pc.val]'(by exact pc.isLt))

/-- The host contains the full unused-position sampler. -/
theorem freshQueryBlock_choice (host : Machine) (attempts : Nat)
    (labels : Fin 115 → Fin (host.size + 1)) (present : ContainsFreshQuery host attempts labels) :
    ContainsFreshChoice host attempts (labels ∘ freshQueryChoiceLabels) := by
  intro pc valid
  have inside : freshQueryChoiceLabels pc ≠ 114 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [freshQueryChoiceLabels] at values
    omega
  exact (present (freshQueryChoiceLabels pc) inside).trans
    ((congrArg (relocate labels) (freshQuery_choice attempts pc valid)).trans
      (relocate_comp freshQueryChoiceLabels labels _))

/-- The host contains the full output transposition scan. -/
theorem freshQueryBlock_swap (host : Machine) (attempts : Nat)
    (labels : Fin 115 → Fin (host.size + 1)) (present : ContainsFreshQuery host attempts labels) :
    ContainsSwapTable host (labels ∘ freshQuerySwapLabels) := by
  intro pc valid
  have inside : freshQuerySwapLabels pc ≠ 114 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [freshQuerySwapLabels] at values
    omega
  exact (present (freshQuerySwapLabels pc) inside).trans
    ((congrArg (relocate labels) (freshQuery_swap attempts pc valid)).trans
      (relocate_comp freshQuerySwapLabels labels _))

/-- The install labels select the thirty pair-update instructions. -/
def freshInstallLabels (index : Nat) : Fin 115 := ⟨84 + min index 30, by omega⟩

/-- The host contains every pair-installation instruction. -/
theorem freshQueryBlock_install (host : Machine) (attempts : Nat)
    (labels : Fin 115 → Fin (host.size + 1)) (present : ContainsFreshQuery host attempts labels) :
    ContainsLinear host installFresh (labels ∘ freshInstallLabels) := by
  intro index valid
  have bound : index < 30 := valid
  have inside : freshInstallLabels index ≠ 114 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [freshInstallLabels, Nat.min_eq_left (by omega : index ≤ 30)] at values
    omega
  exact (present (freshInstallLabels index) inside).trans
    ((congrArg (relocate labels) (freshQuery_install attempts index valid)).trans
      (LinearInstruction.relocate_emit labels _ _))

/-- The failed fresh query returns to its caller in one instruction. -/
theorem freshQueryBlock_failed [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 115 → Fin (host.size + 1)) (present : ContainsFreshQuery host attempts labels)
    (memory : Memory) (failed : memory.registers 7 = 0#256) :
    runPrefix host 1 ⟨labels 66, memory⟩ =
      PMF.pure (some (false, ⟨labels 114, memory⟩, 1)) := by
  simp [runPrefix, step, present 66 (by decide), freshQuery, relocate, failed, PMF.pure_map]

/-- The accepted fresh query prepares the output scan in five instructions. -/
theorem freshQueryBlock_setup [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 115 → Fin (host.size + 1)) (present : ContainsFreshQuery host attempts labels)
    (memory : Memory) (accepted : memory.registers 7 ≠ 0#256) :
    runPrefix host 5 ⟨labels 66, memory⟩ =
      PMF.pure (some (false, ⟨labels 71, freshOutputInitial memory⟩, 5)) := by
  simp [runPrefix, step, present 66 (by decide), present 67 (by decide), present 68 (by decide),
    present 69 (by decide), present 70 (by decide), freshQuery, relocate, accepted,
    freshOutputInitial, Arithmetic.eval, Function.update_comm, PMF.pure_map]

/-- The deterministic tail returns the accepted state before the caller instruction. -/
theorem freshQueryBlock_tail [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 115 → Fin (host.size + 1)) (present : ContainsFreshQuery host attempts labels)
    (count : Nat) (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.registers 4 = BitVec.ofNat 256 count) :
    runPrefix host ((freshQueryTail count memory).2 - 1) ⟨labels 66, memory⟩ =
      PMF.pure (some (false, ⟨labels 114, (freshQueryTail count memory).1⟩,
        (freshQueryTail count memory).2 - 1)) := by
  by_cases failed : memory.registers 7 = 0#256
  · simpa [freshQueryTail, failed] using freshQueryBlock_failed host attempts labels present memory failed
  · simp only [freshQueryTail, if_neg failed]
    rw [show (swapScan count (swapInitial (freshOutputInitial memory))).2 + 36 - 1 =
      5 + ((swapScan count (swapInitial (freshOutputInitial memory))).2 + 30) by omega,
      prefix_add, freshQueryBlock_setup host attempts labels present memory failed, PMF.pure_bind]
    dsimp only
    rw [prefix_add]
    have scan := swapBlock_prefix host (labels ∘ freshQuerySwapLabels)
      (freshQueryBlock_swap host attempts labels present) count (freshOutputInitial memory) fits
      (by simp [freshOutputInitial, counter])
    change runPrefix host _ ⟨labels 71, freshOutputInitial memory⟩ = _ at scan
    rw [scan, PMF.pure_bind]
    have install := linear_prefix host installFresh (labels ∘ freshInstallLabels)
      (freshQueryBlock_install host attempts labels present)
      (swapScan count (swapInitial (freshOutputInitial memory))).1
    change runPrefix host 30 ⟨labels 84, _⟩ = _ at install
    dsimp only
    change ((runPrefix host 30 ⟨labels 84, _⟩).map _).map _ = _
    rw [install, PMF.pure_map, PMF.pure_map]
    simp [freshInstallLabels, installFresh_memory, show installFresh.length = 30 from rfl,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The fresh query returns with exact sampled memory and unused fuel. -/
theorem freshQueryBlock_run [BN254.FieldCertificate] (host : Machine) (attempts outputCount fuel : Nat)
    (labels : Fin 115 → Fin (host.size + 1)) (present : ContainsFreshQuery host attempts labels)
    (memory : Memory) (countFits : attempts < 2 ^ 256) (outputFits : outputCount < 2 ^ 256)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 outputCount) :
    let reserve := (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
      3 + (20 + (11 * outputCount + 37 + fuel))
    run host (15 + reserve) ⟨labels 0, memory⟩ =
      (freshChoiceSamples attempts memory).bind fun result =>
        let tail := freshQueryTail outputCount (freshChoiceFinal result.1)
        (run host (reserve - (result.2 + 1) - (freshChoiceTailCost result.1 - 1) - (tail.2 - 1))
          ⟨labels 114, tail.1⟩).map
          (Option.map fun final => (final.1,
            final.2 + (tail.2 - 1) + (freshChoiceTailCost result.1 - 1) + (result.2 + 1) + 15)) := by
  dsimp only
  let bound := memory.registers 5 - memory.registers 0
  let reserve := (runtimeTrialCost bound + 2) * attempts + 3 + (20 + (11 * outputCount + 37 + fuel))
  have continued := freshChoiceBlock_run host attempts (11 * outputCount + 37 + fuel)
    (labels ∘ freshQueryChoiceLabels) (freshQueryBlock_choice host attempts labels present) memory countFits
  change run host (15 + reserve) ⟨labels 0, memory⟩ = _ at continued
  rw [continued]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨sampled, cost⟩
  have sampleBound := runtimeSamplerMemory_cost _ _ _ sampled cost supported
  have choiceBound := freshChoiceTailCost_bounds sampled
  have tailBound := freshQueryTail_cost outputCount (freshChoiceFinal sampled)
  have counter : (freshChoiceFinal sampled).registers 4 = BitVec.ofNat 256 outputCount := by
    have same := freshChoice_metadata attempts memory sampled cost supported (4 : Fin 6)
    change (freshChoiceFinal sampled).registers 4 = memory.registers 4 at same
    exact same.trans outputCounter
  have available : (freshQueryTail outputCount (freshChoiceFinal sampled)).2 - 1 ≤
      reserve - (cost + 1) - (freshChoiceTailCost sampled - 1) := by
    dsimp [reserve, bound]
    omega
  change (run host (reserve - (cost + 1) - (freshChoiceTailCost sampled - 1))
    ⟨labels 66, freshChoiceFinal sampled⟩).map _ = _
  conv_lhs => arg 2; arg 2; rw [show
    reserve - (cost + 1) - (freshChoiceTailCost sampled - 1) =
      ((freshQueryTail outputCount (freshChoiceFinal sampled)).2 - 1) +
        (reserve - (cost + 1) - (freshChoiceTailCost sampled - 1) -
          ((freshQueryTail outputCount (freshChoiceFinal sampled)).2 - 1)) by omega]
  rw [run_after_prefix, freshQueryBlock_tail host attempts labels present outputCount
    (freshChoiceFinal sampled) outputFits counter, PMF.pure_bind]
  dsimp only
  simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc, reserve, bound]

end Kriterion.ArgoMAC.ArithmeticSimulator
