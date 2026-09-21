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
not read the removed part. Correctness only ever evaluates a garbled public
value, so the round trip is required only there: a transmitted type may drop a
field that some unreachable public value would have filled. -/
theorem PerfectCorrectness.mapPublic
    {Circuit Input Output Randomness Public Packed EncodingKey Labels Oracle : Type}
    {scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels Oracle}
    {oracle : Randomness → Oracle}
    (correct : PerfectCorrectness scheme oracle)
    (pack : Public → Packed) (unpack : Packed → Public)
    (restores : ∀ answers parameter circuit randomness input labels,
      scheme.evaluate answers
          (unpack (pack (scheme.garble parameter circuit randomness).1)) input labels =
        scheme.evaluate answers (scheme.garble parameter circuit randomness).1 input labels) :
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

/-- This adapter rebases an adversary over the transmitted value onto the
internal value. A source-side game samples the internal value, so pushing it
through `pack` before the adversary reads it gives the adversary exactly the
value the transmitted game would have handed it. -/
def AdaptiveAdversary.rebase {oracle : OracleSpec} {Input Public Packed Labels : Type}
    {Aux : Type} (adversary : AdaptiveAdversary oracle Input Packed Labels Aux)
    (pack : Public → Packed) :
    AdaptiveAdversary oracle Input Public Labels Aux where
  State := adversary.State
  firstQueryBudget := adversary.firstQueryBudget
  secondQueryBudget := adversary.secondQueryBudget
  chooseInput parameter value auxiliary := adversary.chooseInput parameter (pack value) auxiliary
  decide parameter value labels auxiliary state :=
    adversary.decide parameter (pack value) labels auxiliary state

end Kriterion.GarbledCircuit

namespace Kriterion.ArgoMAC.Lamport

open BN254

/-- The evaluator restores the two removed pad bits and the slots that row
identity fixes, so the packed circuit evaluates exactly as the wire circuit
does on every garbled table. -/
theorem packedCircuit_evaluate [FieldCertificate] [GroupCertificate]
    (answers : Garbling.EvaluationOracle) (parameter : Nat) (scalar : NonZeroScalar)
    (tape : Garbling.Randomness) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    wireCircuit.evaluate answers
        (Pipeline.PackedTable.unpack
          (Pipeline.Table.pack (wireCircuit.garble parameter scalar tape).1))
        input labels =
      wireCircuit.evaluate answers (wireCircuit.garble parameter scalar tape).1 input labels := by
  simp [wireCircuit, GarbledCircuit.mapLabels, Garbling.garbledCircuit, Garbling.evaluate,
    Garbling.garble, Pipeline.garble]

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
    (fun answers parameter scalar tape input labels =>
      Lamport.packedCircuit_evaluate answers parameter scalar tape input labels)

end Kriterion.ArgoMAC
