/-
This file transfers the scheme obligations across the transmitted-value adapter.
Shrinking the public value changes no game: both experiments are pushed forward
by the same map, and evaluation restores what the map removed.
-/

import Proof.Correctness
import Proof.LamportCompatibility
import Security.AdaptivePrivacy

namespace Kriterion.GarbledCircuit

open Cryptography

/-- A transmitted-value adapter keeps the Lamport encoding obligation. -/
def LamportCompatibility.mapPublic
    {Circuit Input Output Randomness Public Packed EncodingKey Oracle : Type}
    {scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey
      LamportSignature Oracle}
    {inputBits : Input → BitVec 508}
    (compatible : LamportCompatibility scheme inputBits)
    (pack : Public → Packed) (unpack : Packed → Public) :
    LamportCompatibility (scheme.mapPublic pack unpack) inputBits where
  keyPairs := compatible.keyPairs
  encodeSelectsLabels := compatible.encodeSelectsLabels

/-- A transmitted-value adapter keeps perfect correctness when evaluation does
not read the removed part. -/
theorem PerfectCorrectness.mapPublic
    {Circuit Input Output Randomness Public Packed EncodingKey Labels Oracle : Type}
    {scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels Oracle}
    {oracle : Randomness → Oracle}
    (correct : PerfectCorrectness scheme oracle)
    (pack : Public → Packed) (unpack : Packed → Public)
    (restores : ∀ answers value input labels,
      scheme.evaluate answers (unpack (pack value)) input labels =
        scheme.evaluate answers value input labels) :
    PerfectCorrectness (scheme.mapPublic pack unpack) oracle := by
  intro parameter circuit randomness input
  have step := correct parameter circuit randomness input
  simpa only [GarbledCircuit.mapPublic, restores] using step

/-- A transmitted-value adapter for the simulator. -/
noncomputable def Simulator.mapPublic
    {Input Output Public Packed Labels Topology State : Type}
    (simulator : Simulator Input Output Public Labels Topology State)
    (pack : Public → Packed) :
    Simulator Input Output Packed Labels Topology State :=
  ⟨fun parameter topology => (simulator.simulateGarble parameter topology).map
      (fun result => (pack result.1, result.2)),
    simulator.simulateEncode⟩

/-- A transmitted-value adapter preserves every oracle-state obligation. -/
theorem OracleSimulation.mapPublic
    {FixedIndex EncIndex Input Output Public Packed Labels Topology State : Type}
    {simulator : Simulator Input Output Public Labels Topology State}
    {handler : OracleHandler (publicOracleSpec FixedIndex EncIndex) State}
    {view : State → PublicOracle FixedIndex EncIndex}
    (rules : OracleSimulation simulator handler view) (pack : Public → Packed) :
    OracleSimulation (simulator.mapPublic pack) handler view := by
  obtain ⟨valid, seen, initial, query, encode⟩ := rules
  refine ⟨valid, seen, ?_, query, encode⟩
  intro parameter topology result member
  dsimp only [Simulator.mapPublic] at member
  rw [PMF.support_map] at member
  obtain ⟨original, originalMember, rfl⟩ := member
  exact initial parameter topology original originalMember

/-- A transmitted-value adapter preserves the advantage bound: both experiments
are the same games composed with the same map. -/
theorem ConcreteAdaptivePrivacy.mapPublic
    {oracle : OracleSpec} {Circuit Input Output Randomness Public Packed Key Labels
      EvaluationOracle Topology State Aux : Type}
    {scheme : GarbledCircuit Circuit Input Output Randomness Public Key Labels EvaluationOracle}
    {topology : Circuit → Topology} {simulator : Simulator Input Output Public Labels Topology State}
    {randomTape : Nat → PMF Randomness} {realOracle : OracleHandler oracle Randomness}
    {idealOracle : OracleHandler oracle State} {bits : Nat}
    (privacy : ConcreteAdaptivePrivacy (Aux := Aux) scheme topology simulator randomTape
      realOracle idealOracle bits)
    (pack : Public → Packed) (unpack : Packed → Public) :
    ConcreteAdaptivePrivacy (Aux := Aux) (scheme.mapPublic pack unpack) topology
      (simulator.mapPublic pack) randomTape realOracle idealOracle bits := by
  intro adversary circuit auxiliary parameter
  let original : AdaptiveAdversary oracle Input Public Labels Aux :=
    ⟨adversary.State, adversary.firstQueryBudget, adversary.secondQueryBudget,
      fun parameter value auxiliary => adversary.chooseInput parameter (pack value) auxiliary,
      fun parameter value labels => adversary.decide parameter (pack value) labels⟩
  simpa only [realGame, idealGame, GarbledCircuit.mapPublic, Simulator.mapPublic,
    PMF.bind_map, Function.comp_def, adversaryWork, original]
    using privacy original circuit auxiliary parameter

end Kriterion.GarbledCircuit

namespace Kriterion.ArgoMAC.Lamport

open BN254

/-- The evaluator restores the two removed pad bits, so the packed circuit
evaluates exactly as the wire circuit does. -/
theorem packedCircuit_evaluate [FieldCertificate] [GroupCertificate]
    (answers : Garbling.EvaluationOracle) (value : Pipeline.Table)
    (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    wireCircuit.evaluate answers (Pipeline.PackedTable.unpack (Pipeline.Table.pack value))
        input labels =
      wireCircuit.evaluate answers value input labels := by
  simp [wireCircuit, GarbledCircuit.mapLabels, Garbling.garbledCircuit, Garbling.evaluate]

/-- The wire circuit is perfectly correct. -/
theorem wirePerfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness wireCircuit
      (fun randomness =>
        (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)) := by
  intro parameter scalar tape input
  change some (Garbling.evaluate _ _ (restore input
    (selectedLabels (tape.inputMacKey.encodeAffine input)))) = _
  rw [restore_selected]
  exact RCBComplete.perfectCorrectness parameter scalar tape input

/-- The packed circuit keeps the Lamport encoding obligation. -/
def packedCompatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility packedCircuit affineLamportBits :=
  compatible.mapPublic Pipeline.Table.pack Pipeline.PackedTable.unpack

end Kriterion.ArgoMAC.Lamport

namespace Kriterion.ArgoMAC

open BN254

/-- Every random tape gives the required evaluation result for the packed circuit. -/
theorem packedPerfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness Lamport.packedCircuit
      (fun randomness =>
        (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)) :=
  Lamport.wirePerfectCorrectness.mapPublic
    Pipeline.Table.pack Pipeline.PackedTable.unpack
    (fun answers value input labels => Lamport.packedCircuit_evaluate answers value input labels)

end Kriterion.ArgoMAC
