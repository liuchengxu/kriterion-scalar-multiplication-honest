import Proof.Privacy.Simulator.Arithmetic.PermutationForward
import Proof.Privacy.Simulator.Arithmetic.FreshQuerySource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The known-query scan returns the source output or the unused input position. -/
theorem knownQueryScan_source [BN254.FieldCertificate]
    (inputs outputs : List (Word × Word)) (memory : Memory)
    (inputFits : inputs.length < 2 ^ 256) (outputFits : outputs.length < 2 ^ 256)
    (inputCounter : memory.registers 2 = BitVec.ofNat 256 inputs.length)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 outputs.length)
    (inputStored : RepresentsPairs memory.ram (memory.registers 1) inputs)
    (outputStored : RepresentsPairs memory.ram (memory.registers 3) outputs) :
    let position := (swaps inputs).symm (memory.registers 8)
    ((knownQueryScan inputs.length outputs.length memory).1.registers 8,
      (knownQueryScan inputs.length outputs.length memory).1.registers 7) =
      if position.toNat < (memory.registers 0).toNat then (swaps outputs position, 1#256)
      else (position, 0#256) := by
  have source := knownQuery_source inputs outputs memory inputFits outputFits
    inputCounter outputCounter inputStored outputStored
  rw [knownQuery_run inputs.length outputs.length memory inputFits outputFits inputCounter outputCounter,
    PMF.pure_map] at source
  have supported := congrArg PMF.support source
  simpa using supported

/-- The fresh source returns the output permutation of the sampled unused position. -/
theorem freshTailSamples_reply [BN254.FieldCertificate] (attempts : Nat) (outputs : List (Word × Word)) (memory : Memory)
    (stored : RepresentsPairs memory.ram (memory.registers 3) outputs)
    (safeCells : ∀ index, index < 2 * outputs.length →
      8 ≤ (memory.registers 3 + BitVec.ofNat 256 index).toNat) :
    (freshChoiceSamples attempts memory).map
      (fun result => queryValue (freshQueryTail outputs.length (freshChoiceFinal result.1)).1) =
      (Security.BoundedIntegerSampling.cutoff
        (runtimeRange (memory.registers 5 - memory.registers 0)) attempts).law.map
          (Option.map fun rank => swaps outputs (BitVec.ofNat 256 rank.val + memory.registers 0)) := by
  have same : (freshChoiceSamples attempts memory).map
      (fun result => queryValue (freshQueryTail outputs.length (freshChoiceFinal result.1)).1) =
      ((freshChoiceSamples attempts memory).map
        (fun result => freshChoiceValue (freshChoiceFinal result.1))).map (Option.map (swaps outputs)) := by
    rw [PMF.map_comp]
    change (freshChoiceSamples attempts memory).bind _ = (freshChoiceSamples attempts memory).bind _
    apply Security.ThreePhase.bind_eq_on_support
    intro result supported
    dsimp only [Function.comp_def]
    rw [freshQueryTail_value attempts memory result.1 result.2 supported outputs stored safeCells]
  rw [same, freshChoiceSamples_source, PMF.map_comp]
  simp only [Function.comp_def, Option.map_map]

/-- The complete forward source uses the known reply or the exact bounded-retry law. -/
theorem permutationForwardSamples_reply [BN254.FieldCertificate]
    (attempts : Nat) (inputs outputs : List (Word × Word)) (memory : Memory)
    (inputFits : inputs.length < 2 ^ 256) (outputFits : outputs.length < 2 ^ 256)
    (inputCounter : memory.registers 2 = BitVec.ofNat 256 inputs.length)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 outputs.length)
    (inputStored : RepresentsPairs memory.ram (memory.registers 1) inputs)
    (outputStored : RepresentsPairs memory.ram (memory.registers 3) outputs)
    (safeCells : ∀ index, index < 2 * outputs.length →
      8 ≤ (memory.registers 3 + BitVec.ofNat 256 index).toNat) :
    (permutationForwardSamples attempts inputs.length outputs.length memory).map
      (fun result => queryValue result.1) =
      let position := (swaps inputs).symm (memory.registers 8)
      if position.toNat < (memory.registers 0).toNat then PMF.pure (some (swaps outputs position))
      else (Security.BoundedIntegerSampling.cutoff
        (runtimeRange (memory.registers 5 - memory.registers 0)) attempts).law.map
          (Option.map fun rank => swaps outputs (BitVec.ofNat 256 rank.val + memory.registers 0)) := by
  let known := knownQueryScan inputs.length outputs.length memory
  have source := knownQueryScan_source inputs outputs memory inputFits outputFits inputCounter outputCounter inputStored outputStored
  change (known.1.registers 8, known.1.registers 7) = _ at source
  dsimp only
  by_cases member : ((swaps inputs).symm (memory.registers 8)).toNat < (memory.registers 0).toNat
  · rw [if_pos member] at source ⊢
    have value := congrArg Prod.fst source
    have flag := congrArg Prod.snd source
    simp only [Prod.fst, Prod.snd] at value flag
    change (if known.1.registers 7 = 0#256 then _ else PMF.pure (known.1, known.2 + 1)).map _ = _
    simp [flag, PMF.pure_map, queryValue, value]
  · rw [if_neg member] at source ⊢
    have flag := congrArg Prod.snd source
    simp only [Prod.snd] at flag
    change (if known.1.registers 7 = 0#256 then _ else PMF.pure (known.1, known.2 + 1)).map _ = _
    rw [if_pos flag, PMF.map_comp]
    change (freshChoiceSamples attempts known.1).map
      (fun result => queryValue (freshQueryTail outputs.length (freshChoiceFinal result.1)).1) = _
    have base : known.1.registers 3 = memory.registers 3 := knownQueryScan_metadata _ _ _ 3 (by decide)
    have stored : RepresentsPairs known.1.ram (known.1.registers 3) outputs := by
      rw [(knownQueryScan_data inputs.length outputs.length memory).1, base]
      exact outputStored
    rw [freshTailSamples_reply attempts outputs known.1 stored (by simpa only [base] using safeCells)]
    rw [knownQueryScan_metadata _ _ _ 5 (by decide), knownQueryScan_metadata _ _ _ 0 (by decide)]

end Kriterion.ArgoMAC.ArithmeticSimulator
