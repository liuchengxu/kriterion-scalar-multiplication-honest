import Proof.Privacy.Source.SharedRealSourceSum
import Construction.ArgoMAC.Encoding
import Proof.Privacy.Simulator.Arithmetic.PhaseMachineRun
import Proof.Privacy.Simulator.Arithmetic.AdaptiveCutoff
import Proof.SharedOracle

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security GarbledCircuit.SimulatorProtocol
noncomputable section

/-- The option transformer retains the same cutoff branches. -/
theorem optionT_run_bind_cutoff {A B : Type} (distribution : OptionT PMF A)
    (next : A → OptionT PMF B) :
    (distribution >>= next).run = bindCutoff distribution.run (fun value => (next value).run) := by
  rw [OptionT.run_bind]
  unfold Option.elimM bindCutoff
  congr 1
  funext result
  cases result <;> rfl

/-- The setup parser retains the public table, private memory, and fixed oracle. -/
def lazyParsedSetup [FieldCertificate] (machine : Simulator) (parameter : Nat) :
    PMF (Option (Pipeline.PackedTable × Memory × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)) :=
  (simulatorMemoryRun machine machine.firstFuel
    {bits := fun stack => if stack = 0 then [false, false] ++ natural parameter ++ natural 8887896 else []}
    LazyOracle.empty).map fun result => result.bind fun result =>
      (publicValue Wire.encoding 8887896 (result.1.bits 3)).map fun table => (table, result.1, result.2.1)

/-- The online parser retains the wire labels and fixed oracle. -/
def lazyParsedOnline [FieldCertificate] (machine : Simulator) (memory : Memory)
    (input : AffineInput) (value : Option Point)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    PMF (Option (GarbledCircuit.LamportSignature × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)) :=
  (simulatorMemoryRun machine machine.secondFuel
    {memory with bits := Function.update (Function.update memory.bits 0
      ([false, true] ++ affine input ++ output value)) 3 []} oracle).map fun result => result.bind fun result =>
        (words 128 508 (result.1.bits 3)).map fun labels => (labels, result.2.1)

/-- The chosen-input continuation uses the fixed oracle before and after encoding. -/
def lazyChosenDecision [FieldCertificate] [GroupCertificate] {Aux : Type}
    (machine : Simulator)
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)
    (memory : Memory) (table : Pipeline.PackedTable)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) : PMF Bool :=
  (LazyOracle.run (adversary.chooseInput parameter table auxiliary) oracle).bind fun selected =>
    (lazyParsedOnline machine memory selected.1.1
      (Shared.packedProgramCircuit.function scalar selected.1.1) selected.2).bind fun encoded => match encoded with
    | none => PMF.pure false
    | some encoded =>
        (LazyOracle.run (adversary.decide parameter table encoded.1 auxiliary selected.1.2) encoded.2).map Prod.fst

set_option backward.isDefEq.respectTransparency false in
/-- The fixed oracle serves both adversary phases outside the simulator. -/
theorem lazyParsedGame_phases [FieldCertificate] [GroupCertificate] {Aux : Type}
    (machine : Simulator)
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    GarbledCircuit.LazySimulatorProtocol.idealGame Shared.packedProgramCircuit Wire.encoding 8887896 machine
      adversary parameter scalar auxiliary =
    (lazyParsedSetup machine parameter).bind (fun setup => match setup with
      | none => PMF.pure false
      | some setup => lazyChosenDecision machine adversary parameter scalar auxiliary setup.2.1 setup.1 setup.2.2) := by
  have lifted {Result : Type} (distribution : PMF Result) :
      (liftM distribution : OptionT PMF Result).run = distribution.map some := rfl
  have zero (size : Nat) : (⟨0, Nat.zero_lt_succ size⟩ : Fin (size + 1)) = 0 := by
    apply Fin.ext
    simp
  simp only [GarbledCircuit.LazySimulatorProtocol.idealGame, lazyParsedSetup, lazyParsedOnline, lazyChosenDecision,
    simulatorMemoryRun, simulatorStart, zero, optionT_run_bind_cutoff, OptionT.run_mk,
    OptionT.run_pure, bindCutoff, lifted, PMF.bind_map, PMF.map_bind, PMF.bind_bind,
    PMF.pure_bind, PMF.map_comp, Function.comp_def]
  congr 1
  funext setup
  cases setup with
  | none => simp [PMF.pure_map]
  | some setup =>
      cases parsed : publicValue Wire.encoding 8887896 (setup.1.memory.bits 3) with
      | none => simp [parsed, PMF.pure_map]
      | some table =>
          simp only [Option.bind_some, Option.map_some, parsed, PMF.pure_bind]
          rw [PMF.map_bind]
          congr 1
          funext selected
          rw [PMF.map_bind]
          congr 1
          funext encoded
          cases encoded with
          | none => simp [PMF.pure_map]
          | some encoded =>
              cases labels : words 128 508 (encoded.1.memory.bits 3) <;>
                simp [labels, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
