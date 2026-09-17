import Proof.Privacy.Simulator.SimulatorFiniteArithmetic
import Proof.Privacy.Simulator.SimulatorCutoff

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions OperationalOracle
open SimulatorSampling BoundedIntegerSampling
namespace SimulatorMachine
noncomputable section

/-- This relation bounds the full successful output distribution. -/
def CutoffLaw {A : Type} (attempts count : Nat) (exact : PMF A) (finite : PMF (Option A)) : Prop :=
  (∀ value, retained attempts ^ count * exact value ≤ finite (some value)) ∧
    (∀ value, finite (some value) ≤ exact value)

/-- A finite private sampler satisfies the output relation. -/
theorem CutoffLaw.code {A : Type} {count : Nat} (attempts : Nat) (code : Code A count) :
    CutoffLaw attempts count code.law (code.cutoff attempts).law :=
  ⟨code.cutoff_lower attempts, code.cutoff_upper attempts⟩

end
end SimulatorMachine
end Kriterion.ArgoMAC.Security
