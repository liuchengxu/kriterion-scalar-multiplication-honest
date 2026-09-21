import Proof.Privacy.Simulator.Arithmetic.HistoryFreshBlock
import Proof.Privacy.Simulator.Arithmetic.HistoryFreshSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The standalone freshness machine contains all instructions before its return. -/
theorem historyFresh_self : ContainsHistoryFresh historyFresh id := by
  intro pc inside
  change historyFresh.code[pc.val] = relocate id (historyFresh.code[pc.val])
  generalize historyFresh.code[pc.val] = instruction
  cases instruction <;> rfl

/-- The complete machine returns its exact freshness source and instruction charge. -/
theorem historyFresh_run [BN254.FieldCertificate] (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.ram (historyHeader memory) = BitVec.ofNat 256 count) :
    run historyFresh ((historyFreshSource count memory).2 + 1) ⟨0, memory⟩ =
      PMF.pure (some (⟨41, (historyFreshSource count memory).1⟩, (historyFreshSource count memory).2 + 1)) := by
  have checked := historyFreshBlock_continue historyFresh id historyFresh_self count memory fits counter 1
  change run historyFresh ((historyFreshSource count memory).2 + 1) ⟨0, memory⟩ =
    (run historyFresh 1 ⟨41, (historyFreshSource count memory).1⟩).map
      (Option.map fun result => (result.1, result.2 + (historyFreshSource count memory).2)) at checked
  rw [checked]
  have halt (base : Memory) : run historyFresh 1 ⟨41, base⟩ = PMF.pure (some (⟨41, base⟩, 1)) := by
    simp [run, step, historyFresh]
  rw [halt, PMF.pure_map]
  simp [Nat.add_comm]

/-- The complete charge includes all table entries and the final halt. -/
theorem historyFresh_budget (count : Nat) (memory : Memory) :
    historyFresh.size + 1 + ((historyFreshSource count memory).2 + 1) ≤ 12 * count + 67 := by
  have cost := historyFreshSource_cost count memory
  change 42 + 1 + ((historyFreshSource count memory).2 + 1) ≤ _
  omega

/-- The machine accepts exactly fresh requested domain and range pairs. -/
theorem historyFresh_accepts [BN254.FieldCertificate] (pairs : List (Word × Word)) (memory : Memory)
    (fits : pairs.length < 2 ^ 256)
    (counter : memory.ram (historyHeader memory) = BitVec.ofNat 256 pairs.length)
    (stored : RepresentsPairs memory.ram (historyHeader memory + 256#256) pairs) :
    (run historyFresh ((historyFreshSource pairs.length memory).2 + 1) ⟨0, memory⟩).map
      (Option.map fun result => result.1.memory.registers 7 = 1) =
      PMF.pure (some ((∀ pair ∈ pairs, pair.1 ≠ memory.registers 8) ∧
        (∀ pair ∈ pairs, pair.2 ≠ memory.ram 14))) := by
  rw [historyFresh_run pairs.length memory fits counter, PMF.pure_map]
  simp only [Option.map_some, propext (historyFreshSource_accepts pairs memory stored)]

end Kriterion.ArgoMAC.ArithmeticSimulator
