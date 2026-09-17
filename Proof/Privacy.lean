import Construction
import Solution
import Proof.Correctness
import Proof.Privacy.ConcreteSmallSourceRatio
import Proof.Privacy.PaperConstruction
import Proof.Privacy.Simulator.SimulatorTotalImplementation

namespace Kriterion.ArgoMAC.Security

open BN254

/-- This is the adaptive-privacy field of the obligation for the ArgoMAC construction. -/
def AdaptivePrivacy : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field),
    ∃ simulator : GarbledCircuit.Simulator AffineInput (Option (@Point field)) Pipeline.Table
      Garbling.Labels Garbling.Topology CircuitSimulatorState,
      GarbledCircuit.ConcreteAdaptivePrivacy (Aux := Unit)
        (@Garbling.garbledCircuit field group construction) Garbling.topology simulator
        (@uniformRandomTape Garbling.Randomness (@Fintype.ofFinite _ inferInstance)
          (Seed.randomness 0))
        Garbling.oracleHandler circuitSimulatorOracleHandler 100

/-- The checked simulator gives the required universal privacy bound. -/
theorem adaptivePrivacy : AdaptivePrivacy := by
  intro field group
  letI := field
  letI := group
  refine ⟨concreteCircuitSimulator, ?_⟩
  have instances : (@Fintype.ofFinite Garbling.Randomness inferInstance) =
      garblingRandomnessFintype := Subsingleton.elim _ _
  have tapes : @uniformRandomTape Garbling.Randomness (@Fintype.ofFinite _ inferInstance)
      (Seed.randomness 0) = randomTape (Seed.randomness 0) := by
    unfold uniformRandomTape randomTape
    rw [Cryptography.uniformTape_eq, instances]
  rw [tapes]
  exact concreteAdaptivePrivacy (Seed.randomness 0)

/-- The circuit topology does not depend on the scalar. -/
theorem topologyConstant (first second : NonZeroScalar) :
    Garbling.topology first = Garbling.topology second := rfl

end Kriterion.ArgoMAC.Security
