import Proof.Privacy.Simulator.Arithmetic.Blocks

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The charged result retains its memory and next label. -/
def chargedResult {labels : Nat} (initialCost : Nat) (result : Memory × Nat × Fin labels) :
    Memory × Nat × Fin labels := (result.1, initialCost + result.2.1, result.2.2)

/-- A fixed initialCost charge distributes over a complete source continuation. -/
theorem chargedContinuation [BN254.FieldCertificate] {size : Nat} (host : Machine)
    (labels : Fin size → Fin (host.size + 1)) (source : PMF (Memory × Nat × Fin size))
    (initialCost reserve : Nat) :
    (source.bind fun result =>
      (run host (reserve - result.2.1) ⟨labels result.2.2, result.1⟩).map
        (Option.map fun final => (final.1, final.2 + result.2.1))).map
      (Option.map fun final => (final.1, final.2 + initialCost)) =
    (source.map (chargedResult initialCost)).bind fun result =>
      (run host (initialCost + reserve - result.2.1) ⟨labels result.2.2, result.1⟩).map
        (Option.map fun final => (final.1, final.2 + result.2.1)) := by
  rw [PMF.map_bind, PMF.bind_map]
  congr 1
  funext result
  simp only [chargedResult, PMF.map_comp, Option.map_map, Function.comp_def]
  have rest : initialCost + reserve - (initialCost + result.2.1) = reserve - result.2.1 := by omega
  rw [rest]
  congr 1
  funext outcome
  cases outcome with
  | none => rfl
  | some outcome =>
      simp only [Option.map_some]
      rw [Nat.add_assoc, Nat.add_comm result.2.1 initialCost]

end Kriterion.ArgoMAC.ArithmeticSimulator
