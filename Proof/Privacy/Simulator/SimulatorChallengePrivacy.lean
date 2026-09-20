import Proof.Privacy.Simulator.SimulatorTotalImplementation
import Construction.ArgoMAC.Encoding
import Proof.Correctness
import Proof.LamportCompatibility
import Proof.PackedAdapter

namespace Kriterion.ArgoMAC.Security.SimulatorMachine.TotalImplementation
open BN254 Cryptography Cryptography.Assumptions

/-- One allowance covers the abstract simulation and the finite sampling error. -/
theorem privacyWithImplementationError [FieldCertificate] [GroupCertificate]
    {Aux : Type} (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) (witness : Garbling.Randomness) :
    WorkPerAdvantage 100
      (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter + 1)
      (advantage (ThreePhase.realGame adversary parameter scalar auxiliary witness)
        (operationalIdealGame adversary parameter scalar auxiliary) +
       advantage (operationalIdealGame adversary parameter scalar auxiliary)
        (game 256 adversary parameter scalar auxiliary)) := by
  let queries := adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
    adversary.decisionQueryBudget parameter
  have second := game_error adversary parameter scalar auxiliary
  by_cases small : queries < 2 ^ 100
  · have first := operational_small_error adversary parameter scalar auxiliary witness small
    exact (mul_le_mul_of_nonneg_right (add_le_add first second) (by positivity)).trans
      (cutoffEnvelope_has100Bits queries)
  · have first := decisionAdvantage_le_one
      (ThreePhase.realGame adversary parameter scalar auxiliary witness)
      (operationalIdealGame adversary parameter scalar auxiliary)
    have large : (2 : ℝ) ^ 100 ≤ queries := by exact_mod_cast Nat.le_of_not_gt small
    have bound : WorkPerAdvantage 100 (queries + 1) (1 + cutoffResidual queries) := by
      unfold WorkPerAdvantage cutoffResidual
      simp only [Nat.cast_add, Nat.cast_one]
      norm_num at large ⊢
      have realLarge : (1267650600228229401496703205376 : ℝ) ≤ (queries : ℝ) := by
        exact_mod_cast large
      linarith
    exact (mul_le_mul_of_nonneg_right (add_le_add first second) (by positivity)).trans bound

open GarbledCircuit

noncomputable section

/-- The adapter retains the original labels and adds an empty first phase. The
three-phase games sample the internal table, so the adapter hands the adversary
the transmitted value of that table. -/
def wireAdversary {Aux : Type}
    (adversary : AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.PackedTable LamportSignature Aux) :
    ThreePhase.Adversary Aux where
  Before := Unit
  After := adversary.State
  preQueryBudget _ := 0
  inputQueryBudget := adversary.firstQueryBudget
  decisionQueryBudget := adversary.secondQueryBudget
  prepare _ _ := .pure (PMF.pure ())
  chooseInput parameter table auxiliary _ :=
    adversary.chooseInput parameter (Pipeline.Table.pack table) auxiliary
  decide parameter table labels auxiliary state :=
    adversary.decide parameter (Pipeline.Table.pack table)
      (Lamport.selectedLabels labels.inputMac) auxiliary state

def wireSimulator [FieldCertificate] [GroupCertificate] :=
  concreteCircuitSimulator.mapLabels (fun labels => Lamport.selectedLabels labels.inputMac)
    (fun _ : Nat => (⟨508, 91⟩ : Garbling.Topology))

/-- The wire simulator for the transmitted public value. -/
def packedWireSimulator [FieldCertificate] [GroupCertificate] :=
  wireSimulator.mapPublic Pipeline.Table.pack

theorem wire_real [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.PackedTable LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) (witness : Garbling.Randomness) :
    ThreePhase.realGame (wireAdversary adversary) parameter scalar auxiliary witness =
      realGame Lamport.packedCircuit (randomTape witness) Garbling.oracleHandler
        adversary parameter scalar auxiliary := by
  simp only [ThreePhase.realGame, wireAdversary, OracleProgram.run_pure,
    PMF.pure_map, PMF.pure_bind, realGame, Lamport.packedCircuit, GarbledCircuit.mapPublic,
    Lamport.wireCircuit, GarbledCircuit.mapLabels]

theorem wire_ideal [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.PackedTable LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    operationalIdealGame (wireAdversary adversary) parameter scalar auxiliary =
      idealGame Lamport.packedCircuit (fun _ => 8887896) packedWireSimulator
        circuitSimulatorOracleHandler adversary parameter scalar auxiliary := by
  rw [operationalIdealGame_eq]
  simp only [ThreePhase.idealGame, wireAdversary, OracleProgram.run_pure,
    PMF.pure_map, PMF.pure_bind, idealGame, packedWireSimulator, wireSimulator,
    Simulator.mapPublic, Simulator.mapLabels,
    PMF.bind_map, Function.comp_def, concreteCircuitSimulator, circuitSimulator,
    Lamport.packedCircuit, GarbledCircuit.mapPublic, Lamport.wireCircuit,
    GarbledCircuit.mapLabels, Garbling.topology]

/-- A machine refinement closes the challenge property without another error allowance. -/
theorem adaptivePrivacy_of_machine [FieldCertificate] [GroupCertificate]
    [Fintype Pipeline.FixedKeyIndex] [Fintype EncPRF.PermutationIndex] {Aux : Type}
    (witness : Garbling.Randomness) (machine : BoundedMachine.Machine)
    (implementation : ∀ (adversary : AdaptiveAdversary Garbling.oracleSpec
        AffineInput Pipeline.PackedTable LamportSignature Aux) parameter scalar auxiliary,
      SimulatorProtocol.idealGame Lamport.packedCircuit Kriterion.ArgoMAC.Wire.encoding 8887896 machine
        adversary parameter scalar auxiliary =
      game 256 (wireAdversary adversary) parameter scalar auxiliary) :
    AdaptivePrivacy (Aux := Aux) Lamport.packedCircuit Kriterion.ArgoMAC.Wire.encoding 8887896 (randomTape witness)
      Garbling.oracleHandler circuitSimulatorOracleHandler CircuitSimulatorState.view := by
  refine ⟨packedWireSimulator, machine, concreteCircuitSimulator_rules.mapLabels _ _ |>.mapPublic
    Pipeline.Table.pack, ?_⟩
  intro adversary parameter scalar auxiliary
  have bound := privacyWithImplementationError (wireAdversary adversary)
    parameter scalar auxiliary witness
  rw [wire_real, wire_ideal, ← implementation] at bound
  simpa only [wireAdversary, Nat.zero_add, adversaryWork] using bound

end
end Kriterion.ArgoMAC.Security.SimulatorMachine.TotalImplementation
