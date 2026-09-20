import Proof.Privacy.Simulator.Arithmetic.SharedFiniteSourcePhases
import Proof.Privacy.Simulator.Arithmetic.ParsedProgramSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine GarbledCircuit.SimulatorProtocol
noncomputable section
attribute [local irreducible] runProgram

/-- The setup parser retains the complete public table and machine state. -/
def sharedParsedSetup [FieldCertificate] (machine : Machine) (parameter : Nat) : PMF (Option (Pipeline.PackedTable × State)) :=
  (respond machine ([false, false] ++ natural parameter ++ natural 8887896) (initial machine)).map
    (fun result => result.bind fun result => (publicValue Wire.encoding 8887896 result.1).map fun table => (table, result.2))

/-- The online parser retains the exact selected wire labels and machine state. -/
def sharedParsedOnline [FieldCertificate] (machine : Machine) (state : State)
    (input : AffineInput) (value : Option Point) : PMF (Option (GarbledCircuit.LamportSignature × State)) :=
  (respond machine ([false, true] ++ affine input ++ output value) state).map
    (fun result => result.bind fun result => (words 128 508 result.1).map fun labels => (labels, result.2))

/-- The actual protocol uses the same four parsed phase boundaries as the finite source. -/
theorem sharedParsedGame_phases [FieldCertificate] [GroupCertificate] {Aux : Type}
    (machine : Machine)
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    GarbledCircuit.SimulatorProtocol.idealGame Shared.packedCircuit Wire.encoding 8887896 machine adversary parameter scalar auxiliary =
      (bindCutoff (sharedParsedSetup machine parameter) fun setup =>
        bindCutoff (runProgram machine (adversary.chooseInput parameter setup.1 auxiliary) setup.2).run fun selected =>
          bindCutoff (sharedParsedOnline machine selected.2 selected.1.1 (Shared.wireCircuit.function scalar selected.1.1)) fun encoded =>
            ((runProgram machine (adversary.decide parameter setup.1 encoded.1 auxiliary selected.1.2) encoded.2).run).map
              (Option.map Prod.fst)).map (fun result => result.getD false) := by
  simp only [GarbledCircuit.SimulatorProtocol.idealGame, optionT_run_bind_cutoff, OptionT.run_mk,
    OptionT.run_pure, sharedParsedSetup, sharedParsedOnline, bindCutoff, PMF.bind_map, PMF.bind_bind,
    PMF.map_bind, PMF.pure_bind, PMF.map_comp, Function.comp_def]
  congr 1
  funext setup
  cases setup with
  | none => rfl
  | some setup =>
      cases decoded : publicValue Wire.encoding 8887896 setup.1 with
      | none => simp only [Option.bind_some, decoded, PMF.pure_bind, Option.map_none, Option.bind_none]
      | some table =>
          simp only [decoded, PMF.pure_bind, Option.map_some, Option.bind_some]
          congr 1
          congr 1
          funext selected
          cases selected with
          | none => rfl
          | some selected =>
              dsimp only
              congr 1
              funext encoded
              cases encoded with
              | none => rfl
              | some encoded =>
                  cases labels : words 128 508 encoded.1 <;>
                    simp only [Option.bind_some, labels, PMF.pure_bind, Option.map_none, Option.map_some, Option.bind_none, Option.bind_some]
                  unfold PMF.map
                  congr 1
                  funext decision
                  cases decision <;> rfl

end
end Kriterion.ArgoMAC.ArithmeticSimulator
