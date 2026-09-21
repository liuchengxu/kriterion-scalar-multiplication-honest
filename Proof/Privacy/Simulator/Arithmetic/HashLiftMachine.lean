import Proof.Privacy.Simulator.Arithmetic.HashLiftSource
import Proof.Privacy.Simulator.Arithmetic.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Security Cryptography.BoundedMachine

/-- The standalone lift machine contains the 21-instruction program and one halt. -/
def hashLiftMachine : Machine := linearMachine hashLiftProgram (by rw [hashLiftProgram_length]; decide)

/-- The host lift block returns with its exact fixed instruction charge. -/
theorem hashLiftHost_continue [FieldCertificate] (host : Machine) (labels : Nat → Fin (host.size + 1))
    (present : ContainsLinear host hashLiftProgram labels) (base : Memory) (fuel : Nat) :
    run host (21 + fuel) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels 21, executeLinear hashLiftProgram base⟩).map
        (Option.map fun result => (result.1, result.2 + 21)) := by
  simpa only [hashLiftProgram_length] using linear_continue host hashLiftProgram labels present base fuel

/-- The standalone lift budget includes its table and its final halt. -/
theorem hashLiftMachine_budget : hashLiftMachine.size + 1 + (hashLiftProgram.length + 1) = 44 := rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
