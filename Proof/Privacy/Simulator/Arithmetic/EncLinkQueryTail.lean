import Proof.Privacy.Simulator.Arithmetic.EncLinkTail

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The caller adds the query charge to the exact label-write and control charge. -/
theorem encLinkBlock_queryOutcome [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (memory : Memory) (reserve cost : Nat) (enough : 28 ≤ reserve - cost) :
    (run host (reserve - cost) ⟨labels (encLinkQueryLabels (internalForwardReturn memory)), memory⟩).map
      (Option.map fun result => (result.1, result.2 + cost)) =
      (run host (reserve - (cost + (encLinkAfterQuery memory).2.1))
        ⟨labels (encLinkAfterQuery memory).2.2, (encLinkAfterQuery memory).1⟩).map
          (Option.map fun result => (result.1, result.2 + (cost + (encLinkAfterQuery memory).2.1))) := by
  have splitFuel : reserve - cost = 28 + (reserve - cost - 28) := by omega
  conv_lhs => rw [splitFuel, encLinkBlock_afterQuery host attempts labels present memory (reserve - cost - 28)]
  have restFuel : 28 + (reserve - cost - 28) - (encLinkAfterQuery memory).2.1 =
      reserve - (cost + (encLinkAfterQuery memory).2.1) := by omega
  rw [restFuel]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def]
  congr 1
  funext outcome
  cases outcome with
  | none => rfl
  | some outcome =>
      simp only [Option.map_some]
      rw [Nat.add_assoc, Nat.add_comm (encLinkAfterQuery memory).2.1 cost]

end Kriterion.ArgoMAC.ArithmeticSimulator
