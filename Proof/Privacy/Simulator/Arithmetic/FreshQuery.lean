import Construction.Simulator.FreshQuery
import Proof.Privacy.Simulator.Arithmetic.FreshChoiceBlock
import Proof.Privacy.Simulator.Arithmetic.InstallFresh
import Proof.Privacy.Simulator.Arithmetic.SwapBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The query contains the complete fresh-choice block. -/
theorem freshQuery_choice (attempts : Nat) :
    ContainsFreshChoice (freshQuery attempts) attempts freshQueryChoiceLabels := by
  intro pc inside
  have bound : pc.val < 66 := by
    have small := pc.isLt
    have different : pc.val ≠ 66 := by intro equal; apply inside; exact Fin.ext equal
    omega
  simp [freshQuery, freshQueryChoiceLabels, bound]
  rfl

/-- The query contains the complete output-permutation scan. -/
theorem freshQuery_swap (attempts : Nat) :
    ContainsSwapTable (freshQuery attempts) freshQuerySwapLabels := by
  intro pc inside
  have bound : pc.val < 13 := by
    have small := pc.isLt
    have different : pc.val ≠ 13 := by intro equal; apply inside; exact Fin.ext equal
    omega
  simp [freshQuery, freshQuerySwapLabels, show ¬ pc.val + 71 < 66 by omega,
    show 71 ≤ pc.val + 71 by omega, show pc.val + 71 < 84 by omega]
  rfl

/-- The query contains all thirty installation instructions. -/
theorem freshQuery_install (attempts : Nat) : ContainsLinear (freshQuery attempts) installFresh
    (fun index => ⟨84 + min index 30, by change 84 + min index 30 < 115; omega⟩) := by
  intro index valid
  have bound : index < 30 := valid
  simp [freshQuery, Nat.min_eq_left (by omega : index ≤ 30),
    Nat.min_eq_left (by omega : index + 1 ≤ 30), show ¬ 84 + index < 66 by omega,
    show ¬ 84 + index < 84 by omega, show 84 ≤ 84 + index by omega,
    show 84 + index < 114 by omega, Nat.add_assoc]

/-- The output scan uses the chosen position and the retained output-table metadata. -/
def freshOutputInitial (memory : Memory) : Memory :=
  { memory with registers := Function.update (Function.update (Function.update
      (Function.update memory.registers 6 0) 8 (memory.registers 9))
      9 (memory.registers 3)) 10 (memory.registers 4) }

/-- The failed path returns without installing any permutation pair. -/
theorem freshQuery_failed [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory)
    (failed : memory.registers 7 = 0#256) :
    run (freshQuery attempts) (fuel + 2) ⟨66, memory⟩ =
      PMF.pure (some (⟨114, memory⟩, 2)) := by
  simp [run, step, freshQuery, failed, PMF.pure_map]
  rfl

/-- The successful path prepares the output scan in five instructions. -/
theorem freshQuery_setup [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory)
    (accepted : memory.registers 7 ≠ 0#256) :
    run (freshQuery attempts) (fuel + 5) ⟨66, memory⟩ =
      (run (freshQuery attempts) fuel ⟨71, freshOutputInitial memory⟩).map
        (Option.map fun result => (result.1, result.2 + 5)) := by
  simp [run, step, freshQuery, accepted, freshOutputInitial, Arithmetic.eval,
    Function.update_comm, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]
  rfl

/-- The successful path returns the answer and installs both sparse transpositions. -/
theorem freshQuery_accepted [BN254.FieldCertificate] (attempts count extra : Nat) (memory : Memory)
    (accepted : memory.registers 7 ≠ 0#256) (fits : count < 2 ^ 256)
    (counter : memory.registers 4 = BitVec.ofNat 256 count) :
    run (freshQuery attempts) ((swapScan count (swapInitial (freshOutputInitial memory))).2 + 36 + extra)
      ⟨66, memory⟩ =
      PMF.pure (some (⟨114, installedFresh (swapScan count (swapInitial (freshOutputInitial memory))).1⟩,
        (swapScan count (swapInitial (freshOutputInitial memory))).2 + 36)) := by
  rw [show (swapScan count (swapInitial (freshOutputInitial memory))).2 + 36 + extra =
    ((swapScan count (swapInitial (freshOutputInitial memory))).2 + (30 + (extra + 1))) + 5 by omega,
    freshQuery_setup attempts _ memory accepted]
  have scan := swapBlock_continue (freshQuery attempts) freshQuerySwapLabels (freshQuery_swap attempts)
    count (freshOutputInitial memory) fits (by simp [freshOutputInitial, counter]) (30 + (extra + 1))
  change run (freshQuery attempts) _ ⟨71, freshOutputInitial memory⟩ = _ at scan
  rw [scan]
  have install := installFresh_continue (freshQuery attempts)
    (fun index => ⟨84 + min index 30, by change 84 + min index 30 < 115; omega⟩)
    (freshQuery_install attempts) (swapScan count (swapInitial (freshOutputInitial memory))).1 (extra + 1)
  change run (freshQuery attempts) (30 + (extra + 1)) ⟨84, _⟩ = _ at install
  change ((run (freshQuery attempts) (30 + (extra + 1)) ⟨84, _⟩).map _).map _ = _
  rw [install]
  change (((run (freshQuery attempts) (extra + 1) ⟨114, _⟩).map _).map _).map _ = _
  simp [run, step, freshQuery, PMF.pure_map, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [show 5 + (31 + (swapScan count (swapInitial (freshOutputInitial memory))).2) =
    36 + (swapScan count (swapInitial (freshOutputInitial memory))).2 by omega]

/-- The deterministic tail either returns failure or installs the accepted pair. -/
def freshQueryTail (count : Nat) (memory : Memory) : Memory × Nat :=
  if memory.registers 7 = 0#256 then (memory, 2)
  else let scanned := swapScan count (swapInitial (freshOutputInitial memory))
       (installedFresh scanned.1, scanned.2 + 36)

/-- The tail uses at most eleven instructions per output pair and thirty-eight more. -/
theorem freshQueryTail_cost (count : Nat) (memory : Memory) :
    (freshQueryTail count memory).2 ≤ 11 * count + 38 := by
  unfold freshQueryTail
  split
  · simp
  · have bound := (swapScan_cost count (swapInitial (freshOutputInitial memory))).2
    dsimp only
    omega

/-- Extra fuel does not change the completed deterministic tail. -/
theorem freshQuery_tail [BN254.FieldCertificate] (attempts count extra : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.registers 4 = BitVec.ofNat 256 count) :
    run (freshQuery attempts) ((freshQueryTail count memory).2 + extra) ⟨66, memory⟩ =
      PMF.pure (some (⟨114, (freshQueryTail count memory).1⟩, (freshQueryTail count memory).2)) := by
  by_cases failed : memory.registers 7 = 0#256
  · simpa [freshQueryTail, failed, Nat.add_comm] using freshQuery_failed attempts extra memory failed
  · simpa [freshQueryTail, failed] using freshQuery_accepted attempts count extra memory failed fits counter

/-- The full fresh query retains every sampled path, state update, and actual cost. -/
theorem freshQuery_run [BN254.FieldCertificate] (attempts outputCount : Nat) (memory : Memory)
    (countFits : attempts < 2 ^ 256) (outputFits : outputCount < 2 ^ 256)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 outputCount) :
    run (freshQuery attempts)
      ((runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
        11 * outputCount + 76) ⟨0, memory⟩ =
      (freshChoiceSamples attempts memory).map fun result =>
        let tail := freshQueryTail outputCount (freshChoiceFinal result.1)
        some (⟨114, tail.1⟩,
          tail.2 + (freshChoiceTailCost result.1 - 1) + (result.2 + 1) + 15) := by
  let bound := memory.registers 5 - memory.registers 0
  let reserve := (runtimeTrialCost bound + 2) * attempts + 3 + (20 + (11 * outputCount + 38))
  have continued := freshChoiceBlock_run (freshQuery attempts) attempts (11 * outputCount + 38)
    freshQueryChoiceLabels (freshQuery_choice attempts) memory countFits
  dsimp only at continued
  rw [show (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
    11 * outputCount + 76 = 15 + reserve by dsimp [bound, reserve]; omega]
  change run (freshQuery attempts) (15 + reserve) ⟨freshQueryChoiceLabels 0, memory⟩ = _
  rw [continued]
  change (freshChoiceSamples attempts memory).bind _ = (freshChoiceSamples attempts memory).bind _
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
  have available : (freshQueryTail outputCount (freshChoiceFinal sampled)).2 ≤
      reserve - (cost + 1) - (freshChoiceTailCost sampled - 1) := by
    dsimp [reserve, bound]
    omega
  change (run (freshQuery attempts) (reserve - (cost + 1) - (freshChoiceTailCost sampled - 1))
    ⟨66, freshChoiceFinal sampled⟩).map _ = _
  rw [show reserve - (cost + 1) - (freshChoiceTailCost sampled - 1) =
    (freshQueryTail outputCount (freshChoiceFinal sampled)).2 +
      (reserve - (cost + 1) - (freshChoiceTailCost sampled - 1) -
        (freshQueryTail outputCount (freshChoiceFinal sampled)).2) by omega,
    freshQuery_tail attempts outputCount _ (freshChoiceFinal sampled) outputFits counter,
    PMF.pure_map]
  rfl

/-- The complete fresh query includes its 115-entry table and all sampler work. -/
theorem freshQuery_budget (attempts outputCount : Nat) (memory : Memory) :
    (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
      11 * outputCount + 76 + (freshQuery attempts).size + 1 ≤
        2574 * attempts + 11 * outputCount + 191 := by
  have trial := runtimeTrialCost_bound (memory.registers 5 - memory.registers 0)
  have product := Nat.mul_le_mul_right attempts (show
    runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2 ≤ 2574 by omega)
  change _ + _ + 76 + 114 + 1 ≤ _
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
