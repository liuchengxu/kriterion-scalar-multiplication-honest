import Proof.Privacy.Simulator.Arithmetic.EncLinkRowsCoordinate

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Security Security.SimulatorMachine
noncomputable section

/-- The typed source output has the same x-then-y array layout as the machine. -/
def encLinkMacWords (mac : InputMac) : List Block := mac.x.toList ++ mac.y.toList

/-- The typed link source uses the exact hash followed by the fixed masked row source. -/
theorem encLinkProgram_rows (attempts : Nat) (state : SparseOracleFamily)
    (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac) :
    ((encLinkProgram curve input mac).cutoffLaw (oracleFamilyCutoff attempts) state).map
      (Option.map fun result => (encLinkMacWords result.1, result.2)) =
      (oracleFamilySampled (.inr (curve.result input)) state).bind fun hash =>
        (encLinkRowsProgram (hashFin.symm hash.1).1 (hashFin.symm hash.1).2
          (BitInput.ofAffine input).xBits (BitInput.ofAffine input).yBits (encLinkMacLabels mac)
          (List.finRange 508)).cutoffLaw (oracleFamilyCutoff attempts) hash.2 := by
  rw [encLinkProgram, Program.cutoffLaw, map_bindCutoff]
  simp only [oracleFamilyCutoff, bindCutoff, PMF.bind_map, Function.comp_def]
  apply Security.ThreePhase.bind_eq_on_support
  intro hash supported
  rw [Program.cutoffLaw, map_bindCutoff, encLinkRowsProgram_coordinates]
  apply congrArg (bindCutoff _)
  funext x
  rw [Program.cutoffLaw]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def, encLinkMacWords]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
