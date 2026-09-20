import Construction.Simulator.KnownQuery
import Proof.Privacy.Simulator.Arithmetic.InverseProbeBlock
import Proof.Privacy.Simulator.Arithmetic.SwapBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The query path contains the complete inverse probe. -/
theorem knownQuery_probe : ContainsInverseProbe knownQuery knownProbeLabels := by
  intro pc valid
  fin_cases pc <;> simp_all [knownQuery, knownProbeLabels, inverseProbe, relocate]

/-- The query path contains the complete forward transposition scan. -/
theorem knownQuery_swap : ContainsSwapTable knownQuery knownSwapLabels := by
  intro pc valid
  fin_cases pc <;> simp_all [knownQuery, knownSwapLabels, swapTable, relocate]

/-- The output scan receives its address and count from the preserved caller registers. -/
def knownQueryInitial (memory : Memory) : Memory :=
  { memory with registers := Function.update (Function.update (Function.update memory.registers 6 0)
      9 (memory.registers 3)) 10 (memory.registers 4) }

/-- A fresh query returns its inverse position and its zero flag. -/
theorem knownQuery_fresh [BN254.FieldCertificate] (memory : Memory)
    (fresh : memory.registers 7 = 0#256) :
    run knownQuery 2 ⟨21, memory⟩ = PMF.pure (some (⟨38, memory⟩, 2)) := by
  simp [run, step, knownQuery, fresh, PMF.pure_map]
  rfl

/-- A known query prepares its forward scan in four instructions. -/
theorem knownQuery_setup [BN254.FieldCertificate] (memory : Memory)
    (known : memory.registers 7 ≠ 0#256) (fuel : Nat) :
    run knownQuery (fuel + 4) ⟨21, memory⟩ =
      (run knownQuery fuel ⟨25, knownQueryInitial memory⟩).map
        (Option.map fun result => (result.1, result.2 + 4)) := by
  simp [run, step, knownQuery, known, knownQueryInitial, Arithmetic.eval,
    Function.update_comm, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]
  rfl

/-- The known branch applies the output permutation and retains the complete cost. -/
theorem knownQuery_known [BN254.FieldCertificate] (count : Nat) (memory : Memory)
    (known : memory.registers 7 ≠ 0#256) (fits : count < 2 ^ 256)
    (counter : memory.registers 4 = BitVec.ofNat 256 count) :
    run knownQuery ((swapScan count (swapInitial (knownQueryInitial memory))).2 + 5)
      ⟨21, memory⟩ =
      PMF.pure (some (⟨38, (swapScan count (swapInitial (knownQueryInitial memory))).1⟩,
        (swapScan count (swapInitial (knownQueryInitial memory))).2 + 5)) := by
  rw [show (swapScan count (swapInitial (knownQueryInitial memory))).2 + 5 =
    ((swapScan count (swapInitial (knownQueryInitial memory))).2 + 1) + 4 by omega,
    knownQuery_setup memory known]
  have next := swapBlock_continue knownQuery knownSwapLabels knownQuery_swap
    count (knownQueryInitial memory) fits (by simp [knownQueryInitial, counter]) 1
  change run knownQuery _ ⟨25, knownQueryInitial memory⟩ = _ at next
  rw [next]
  simp [run, step, knownQuery, knownSwapLabels, PMF.pure_map, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rfl

/-- The branch source returns early for a fresh query. -/
def knownQueryBranch (count : Nat) (memory : Memory) : Memory × Nat :=
  if memory.registers 7 = 0#256 then (memory, 2)
  else let result := swapScan count (swapInitial (knownQueryInitial memory))
       (result.1, result.2 + 5)

/-- The complete source composes inverse lookup, the known-input test, and output lookup. -/
def knownQueryScan (inputCount outputCount : Nat) (memory : Memory) : Memory × Nat :=
  let scanned := reverseSwapScan inputCount (reverseSwapInitial (inverseProbeInitial memory))
  let branch := knownQueryBranch outputCount (inverseProbeFinal scanned.1)
  (branch.1, branch.2 + scanned.2 + 8)

/-- The inverse probe preserves the output-table count. -/
theorem inverseProbe_outputCount (inputCount : Nat) (memory : Memory) :
    (inverseProbeFinal (reverseSwapScan inputCount
      (reverseSwapInitial (inverseProbeInitial memory))).1).registers 4 = memory.registers 4 := by
  simp only [inverseProbeFinal, Function.update_of_ne (by decide : (4 : Register) ≠ 7)]
  rw [reverseSwapScan_caller _ _ 4 (by decide)]
  simp [reverseSwapInitial, inverseProbeInitial, executeLinear, inverseProbeSetup,
    LinearInstruction.execute]

/-- The complete machine implements the known-query path with exact memory and cost. -/
theorem knownQuery_run [BN254.FieldCertificate] (inputCount outputCount : Nat) (memory : Memory)
    (inputFits : inputCount < 2 ^ 256) (outputFits : outputCount < 2 ^ 256)
    (inputCounter : memory.registers 2 = BitVec.ofNat 256 inputCount)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 outputCount) :
    run knownQuery (knownQueryScan inputCount outputCount memory).2 ⟨0, memory⟩ =
      PMF.pure (some (⟨38, (knownQueryScan inputCount outputCount memory).1⟩,
        (knownQueryScan inputCount outputCount memory).2)) := by
  let probed := inverseProbeFinal
    (reverseSwapScan inputCount (reverseSwapInitial (inverseProbeInitial memory))).1
  have next := inverseProbeBlock_continue knownQuery knownProbeLabels knownQuery_probe
    inputCount memory inputFits inputCounter (knownQueryBranch outputCount probed).2
  change run knownQuery _ ⟨0, memory⟩ = _ at next
  have reordered : (knownQueryScan inputCount outputCount memory).2 =
      (reverseSwapScan inputCount (reverseSwapInitial (inverseProbeInitial memory))).2 + 8 +
        (knownQueryBranch outputCount probed).2 := by
    dsimp [knownQueryScan, probed]
    omega
  rw [reordered, next]
  change (run knownQuery (knownQueryBranch outputCount probed).2 ⟨21, probed⟩).map _ = _
  by_cases fresh : probed.registers 7 = 0#256
  · simp only [knownQueryBranch, if_pos fresh]
    rw [knownQuery_fresh probed fresh, PMF.pure_map]
    simp [knownQueryScan, knownQueryBranch, probed, fresh, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simp only [knownQueryBranch, if_neg fresh]
    rw [knownQuery_known outputCount probed fresh outputFits
      (by simpa [probed, inverseProbe_outputCount] using outputCounter), PMF.pure_map]
    simp [knownQueryScan, knownQueryBranch, probed, fresh, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The known branch uses at most eleven instructions per output pair and seven final instructions. -/
theorem knownQueryBranch_cost (count : Nat) (memory : Memory) :
    (knownQueryBranch count memory).2 ≤ 11 * count + 7 := by
  unfold knownQueryBranch
  split
  · simp
  · have bound := (swapScan_cost count (swapInitial (knownQueryInitial memory))).2
    dsimp only
    omega

/-- The complete charge includes both scans and all thirty-nine table entries. -/
theorem knownQuery_budget (inputCount outputCount : Nat) (memory : Memory) :
    knownQuery.size + 1 + (knownQueryScan inputCount outputCount memory).2 ≤
      11 * (inputCount + outputCount) + 56 := by
  have inverse := (reverseSwapScan_cost inputCount
    (reverseSwapInitial (inverseProbeInitial memory))).2
  have forward := knownQueryBranch_cost outputCount
    (inverseProbeFinal (reverseSwapScan inputCount
      (reverseSwapInitial (inverseProbeInitial memory))).1)
  change 38 + 1 + _ ≤ _
  dsimp [knownQueryScan]
  omega

/-- The inverse probe preserves RAM. -/
theorem inverseProbe_ram (count : Nat) (memory : Memory) :
    (inverseProbeFinal (reverseSwapScan count
      (reverseSwapInitial (inverseProbeInitial memory))).1).ram = memory.ram := by
  change (reverseSwapScan count (reverseSwapInitial (inverseProbeInitial memory))).1.ram = _
  rw [(reverseSwapScan_data _ _).2]
  rfl

/-- The inverse probe preserves the six metadata registers. -/
theorem inverseProbe_metadata (count : Nat) (memory : Memory) (register : Register)
    (low : register.val < 6) :
    (inverseProbeFinal (reverseSwapScan count
      (reverseSwapInitial (inverseProbeInitial memory))).1).registers register =
      memory.registers register := by
  have notSeven : register ≠ 7 := by intro equal; subst register; norm_num at low
  simp only [inverseProbeFinal, Function.update_of_ne notSeven]
  rw [reverseSwapScan_caller _ _ register (by omega)]
  fin_cases register <;> simp_all [reverseSwapInitial, inverseProbeInitial, executeLinear,
    inverseProbeSetup, LinearInstruction.execute]

/-- A forward scan preserves the caller registers below eight. -/
theorem swapScan_caller (count : Nat) (memory : Memory) (register : Register)
    (low : register.val < 8) :
    (swapScan count memory).1.registers register = memory.registers register := by
  induction count generalizing memory with
  | zero => rfl
  | succ count ih =>
      change (swapScan count (swapMemory memory)).1.registers register = _
      rw [ih]
      fin_cases register <;> simp_all [swapMemory]

/-- The inverse probe state has the source position and the source known-input flag. -/
theorem inverseProbe_state_source [BN254.FieldCertificate]
    (pairs : List (Word × Word)) (memory : Memory) (fits : pairs.length < 2 ^ 256)
    (counter : memory.registers 2 = BitVec.ofNat 256 pairs.length)
    (represented : RepresentsPairs memory.ram (memory.registers 1) pairs) :
    let final := inverseProbeFinal (reverseSwapScan pairs.length
      (reverseSwapInitial (inverseProbeInitial memory))).1
    let position := (Security.OperationalOracle.swaps pairs).symm (memory.registers 8)
    (final.registers 8, final.registers 7) =
      (position, if position.toNat < (memory.registers 0).toNat then 1#256 else 0#256) := by
  have source := inverseProbe_source pairs memory fits counter represented
  dsimp only at source ⊢
  rw [inverseProbe_run pairs.length memory fits counter, PMF.pure_map] at source
  have supported := congrArg PMF.support source
  simpa using supported

/-- The known-query machine returns the source output on every known input. -/
theorem knownQuery_source [BN254.FieldCertificate]
    (inputs outputs : List (Word × Word)) (memory : Memory)
    (inputFits : inputs.length < 2 ^ 256) (outputFits : outputs.length < 2 ^ 256)
    (inputCounter : memory.registers 2 = BitVec.ofNat 256 inputs.length)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 outputs.length)
    (inputStored : RepresentsPairs memory.ram (memory.registers 1) inputs)
    (outputStored : RepresentsPairs memory.ram (memory.registers 3) outputs) :
    let position := (Security.OperationalOracle.swaps inputs).symm (memory.registers 8)
    let known := position.toNat < (memory.registers 0).toNat
    (run knownQuery (knownQueryScan inputs.length outputs.length memory).2 ⟨0, memory⟩).map
      (Option.map fun result => (result.1.memory.registers 8, result.1.memory.registers 7)) =
      PMF.pure (some (if known then
        (Security.OperationalOracle.swaps outputs position, 1#256) else (position, 0#256))) := by
  dsimp only
  let probed := inverseProbeFinal (reverseSwapScan inputs.length
    (reverseSwapInitial (inverseProbeInitial memory))).1
  have probe := inverseProbe_state_source inputs memory inputFits inputCounter inputStored
  change (probed.registers 8, probed.registers 7) = _ at probe
  have position := congrArg Prod.fst probe
  have flag := congrArg Prod.snd probe
  dsimp only at position flag
  have outputValue : (swapScan outputs.length (swapInitial (knownQueryInitial probed))).1.registers 8 =
      Security.OperationalOracle.swaps outputs (probed.registers 8) := by
    rw [swapScan_source]
    have source := applyTableSwaps_source outputs memory.ram (memory.registers 3)
      (probed.registers 8) outputStored
    simpa [swapInitial, knownQueryInitial, probed, inverseProbe_ram, inverseProbe_metadata] using source
  have outputFlag : (swapScan outputs.length (swapInitial (knownQueryInitial probed))).1.registers 7 =
      probed.registers 7 := by
    rw [swapScan_caller _ _ 7 (by decide)]
    simp [swapInitial, knownQueryInitial]
  rw [knownQuery_run inputs.length outputs.length memory inputFits outputFits inputCounter outputCounter,
    PMF.pure_map]
  change PMF.pure (some ((knownQueryBranch outputs.length probed).1.registers 8,
    (knownQueryBranch outputs.length probed).1.registers 7)) = _
  by_cases known : ((Security.OperationalOracle.swaps inputs).symm (memory.registers 8)).toNat <
      (memory.registers 0).toNat
  · have nonzero : probed.registers 7 ≠ 0#256 := by rw [flag]; simp [known]
    simp [knownQueryBranch, nonzero, outputValue, outputFlag, position, flag, known]
  · have zero : probed.registers 7 = 0#256 := by rw [flag]; simp [known]
    simp [knownQueryBranch, zero, position, known]

end Kriterion.ArgoMAC.ArithmeticSimulator
