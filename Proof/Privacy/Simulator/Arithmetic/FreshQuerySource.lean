import Proof.Privacy.Simulator.Arithmetic.FreshQuery
import Proof.Privacy.Simulator.Arithmetic.KnownQuery

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The query observer rejects failed draws and returns accepted answers. -/
def queryValue (memory : Memory) : Option Word :=
  if memory.registers 7 = 0#256 then none else some (memory.registers 8)

/-- The fresh-choice block preserves the represented output table. -/
theorem freshChoice_outputTable (attempts : Nat) (original sampled : Memory) (cost : Nat)
    (supported : (sampled, cost) ∈ (freshChoiceSamples attempts original).support)
    (outputs : List (Word × Word))
    (stored : RepresentsPairs original.ram (original.registers 3) outputs)
    (safeCells : ∀ index, index < 2 * outputs.length →
      8 ≤ (original.registers 3 + BitVec.ofNat 256 index).toNat) :
    RepresentsPairs (freshChoiceFinal sampled).ram (original.registers 3) outputs := by
  apply RepresentsPairs.congr outputs original.ram (freshChoiceFinal sampled).ram (original.registers 3) stored
  intro index bound
  exact freshChoice_ram attempts original sampled cost supported _ (safeCells index bound)

/-- Each fresh-query path returns the output permutation of its chosen unused position. -/
theorem freshQueryTail_value (attempts : Nat) (original sampled : Memory) (cost : Nat)
    (supported : (sampled, cost) ∈ (freshChoiceSamples attempts original).support)
    (outputs : List (Word × Word))
    (stored : RepresentsPairs original.ram (original.registers 3) outputs)
    (safeCells : ∀ index, index < 2 * outputs.length →
      8 ≤ (original.registers 3 + BitVec.ofNat 256 index).toNat) :
    queryValue (freshQueryTail outputs.length (freshChoiceFinal sampled)).1 =
      (freshChoiceValue (freshChoiceFinal sampled)).map (Security.OperationalOracle.swaps outputs) := by
  let chosen := freshChoiceFinal sampled
  have table := freshChoice_outputTable attempts original sampled cost supported outputs stored safeCells
  have base := freshChoice_metadata attempts original sampled cost supported (3 : Fin 6)
  change chosen.registers 3 = original.registers 3 at base
  have value : (swapScan outputs.length (swapInitial (freshOutputInitial chosen))).1.registers 8 =
      Security.OperationalOracle.swaps outputs (chosen.registers 9) := by
    rw [swapScan_source]
    have source := applyTableSwaps_source outputs chosen.ram (original.registers 3) (chosen.registers 9) table
    simpa [swapInitial, freshOutputInitial, base] using source
  have flag : (swapScan outputs.length (swapInitial (freshOutputInitial chosen))).1.registers 7 =
      chosen.registers 7 := by
    rw [swapScan_caller _ _ 7 (by decide)]
    simp [swapInitial, freshOutputInitial]
  change queryValue (freshQueryTail outputs.length chosen).1 = (freshChoiceValue chosen).map _
  by_cases failed : chosen.registers 7 = 0#256
  · simp [freshQueryTail, freshChoiceValue, queryValue, failed]
  · simp [freshQueryTail, freshChoiceValue, queryValue, failed, installedFresh, value, flag]

/-- The full fresh-query answer has the exact bounded-retry sparse-permutation law. -/
theorem freshQuery_source [BN254.FieldCertificate] (attempts : Nat) (outputs : List (Word × Word))
    (memory : Memory) (countFits : attempts < 2 ^ 256) (outputFits : outputs.length < 2 ^ 256)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 outputs.length)
    (stored : RepresentsPairs memory.ram (memory.registers 3) outputs)
    (safeCells : ∀ index, index < 2 * outputs.length →
      8 ≤ (memory.registers 3 + BitVec.ofNat 256 index).toNat) :
    (run (freshQuery attempts)
      ((runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
        11 * outputs.length + 76) ⟨0, memory⟩).map
      (fun result => result.bind fun final => queryValue final.1.memory) =
      (Security.BoundedIntegerSampling.cutoff
        (runtimeRange (memory.registers 5 - memory.registers 0)) attempts).law.map
        (Option.map fun rank => Security.OperationalOracle.swaps outputs
          (BitVec.ofNat 256 rank.val + memory.registers 0)) := by
  rw [freshQuery_run attempts outputs.length memory countFits outputFits outputCounter, PMF.map_comp]
  have same : (freshChoiceSamples attempts memory).map
      (fun result => queryValue (freshQueryTail outputs.length (freshChoiceFinal result.1)).1) =
      ((freshChoiceSamples attempts memory).map
        (fun result => freshChoiceValue (freshChoiceFinal result.1))).map
          (Option.map (Security.OperationalOracle.swaps outputs)) := by
    rw [PMF.map_comp]
    change (freshChoiceSamples attempts memory).bind _ = (freshChoiceSamples attempts memory).bind _
    apply Security.ThreePhase.bind_eq_on_support
    intro result supported
    dsimp only [Function.comp_def]
    rw [freshQueryTail_value attempts memory result.1 result.2 supported outputs stored safeCells]
  change (freshChoiceSamples attempts memory).map
    (fun result => queryValue (freshQueryTail outputs.length (freshChoiceFinal result.1)).1) = _
  rw [same, freshChoiceSamples_source, PMF.map_comp]
  simp [Function.comp_def, Option.map_map]

end Kriterion.ArgoMAC.ArithmeticSimulator
