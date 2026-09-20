import Proof.Privacy.Simulator.Arithmetic.EncLinkWhitening
import Proof.Privacy.Simulator.Arithmetic.EncLinkQueryBody
import Proof.Privacy.Simulator.Arithmetic.ChargedContinuation
import Proof.Privacy.Simulator.Arithmetic.StoredHandlerCost

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The initialization source saves the caller data before it reads the hash oracle. -/
def encLinkSaved (memory : Memory) : Memory := executeLinear encLinkSave memory

/-- The hash continuation records both whitening keys and the fixed schedule. -/
noncomputable def encLinkInitializePost (result : Memory × Nat) : Memory × Nat × Fin 7468 :=
  (encLinkScheduled result.1, result.2 - 1 + 7120, 7208)

/-- The initialization source includes every save, hash, and schedule instruction. -/
noncomputable def encLinkInitializeSamples (count : Nat) (memory : Memory) :
    PMF (Memory × Nat × Fin 7468) :=
  ((hashHandlerSamples count (encLinkSaved memory)).map encLinkInitializePost).map (chargedResult 15)

/-- The host saves all caller inputs in exactly fifteen instructions. -/
theorem encLinkBlock_save [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (memory : Memory) :
    runPrefix host 15 ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels 15, encLinkSaved memory⟩, 15)) := by
  have contains := encLinkBlock_linear host attempts labels present encLinkSave encLinkSaveLabels
    (encLink_save attempts) (by
      intro index valid
      have bound : index < 15 := valid
      simp [encLinkSaveLabels, encLinkLabels, bound]
      omega)
  exact linear_prefix host encLinkSave (labels ∘ encLinkSaveLabels) contains memory

/-- The hash postprocessing preserves the exact spent cost and unused caller fuel. -/
theorem encLinkBlock_initializePost [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (result : Memory × Nat) (reserve : Nat) (enough : 7120 ≤ reserve - (result.2 - 1)) :
    (run host (reserve - (result.2 - 1)) ⟨labels 88, result.1⟩).map
      (Option.map fun final => (final.1, final.2 + (result.2 - 1))) =
    (run host (reserve - (encLinkInitializePost result).2.1)
      ⟨labels (encLinkInitializePost result).2.2, (encLinkInitializePost result).1⟩).map
        (Option.map fun final => (final.1, final.2 + (encLinkInitializePost result).2.1)) := by
  rw [show reserve - (result.2 - 1) = 7120 + (reserve - (result.2 - 1 + 7120)) by omega,
    run_after_prefix, encLinkBlock_schedule host attempts labels present result.1, PMF.pure_bind, PMF.map_comp]
  simp [encLinkInitializePost, Function.comp_def, Option.map_map, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The hash and schedule source returns to the first link row. -/
theorem encLinkBlock_hashInitialize [BN254.FieldCertificate] (host : Machine) (attempts count fuel : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (memory : Memory) (fits : count < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count) :
    let reserve := (hashScan count memory).2 + 1844 + (7120 + fuel)
    run host reserve ⟨labels 15, memory⟩ =
      ((hashHandlerSamples count memory).map encLinkInitializePost).bind fun result =>
        (run host (reserve - result.2.1) ⟨labels result.2.2, result.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.1)) := by
  dsimp only
  have queried := hashHandlerBlock_continue host (labels ∘ encLinkHashLabels)
    (encLinkBlock_hash host attempts labels present) count (7120 + fuel) memory fits counter
  change run host _ ⟨labels 15, memory⟩ = _ at queried
  rw [queried]
  apply mappedContinuation (hashHandlerSamples count memory) encLinkInitializePost
  intro result supported
  have bound := hashHandlerSamples_cost count memory result.1 result.2 supported
  exact encLinkBlock_initializePost host attempts labels present result _ (by omega)

/-- The complete initialization implements its source before the 508-row loop. -/
theorem encLinkBlock_initialize [BN254.FieldCertificate] (host : Machine) (attempts count fuel : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (memory : Memory) (fits : count < 2 ^ 256)
    (counter : (oracleLoaded (encLinkSaved memory)).registers 0 = BitVec.ofNat 256 count) :
    let reserve := 15 + ((hashScan count (encLinkSaved memory)).2 + 1844 + (7120 + fuel))
    run host reserve ⟨labels 0, memory⟩ =
      (encLinkInitializeSamples count memory).bind fun result =>
        (run host (reserve - result.2.1) ⟨labels result.2.2, result.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.1)) := by
  dsimp only
  rw [run_after_prefix, encLinkBlock_save host attempts labels present memory, PMF.pure_bind]
  dsimp only
  rw [encLinkBlock_hashInitialize host attempts count fuel labels present (encLinkSaved memory) fits counter]
  exact chargedContinuation host labels _ 15 _

end Kriterion.ArgoMAC.ArithmeticSimulator
