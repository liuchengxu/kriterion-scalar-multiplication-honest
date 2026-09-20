import Proof.Privacy.Simulator.Arithmetic.EncLinkRowsVector
import Proof.Privacy.Simulator.Arithmetic.EncLinkPositions

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security.SimulatorMachine
noncomputable section

/-- The source label array contains the x labels before the y labels. -/
def encLinkMacLabels (mac : InputMac) (position : Fin 508) : Block :=
  match (encLinkIndexAt position).1 with
  | .x => mac.x[(encLinkIndexAt position).2.val]
  | .y => mac.y[(encLinkIndexAt position).2.val]

/-- The x rows implement the exact typed coordinate source. -/
theorem encLinkRowsProgram_x (attempts : Nat) (state : SparseOracleFamily)
    (firstKey secondKey : Block) (x y : BitVec coordinateBitCount) (mac : InputMac) :
    (encLinkRowsProgram firstKey secondKey x y (encLinkMacLabels mac) (List.ofFn encLinkXPosition)).cutoffLaw
      (oracleFamilyCutoff attempts) state =
      ((encLinkCoordinateProgram ⟨firstKey, secondKey⟩ .x x mac.x).cutoffLaw
        (oracleFamilyCutoff attempts) state).map (Option.map fun result => (result.1.toList, result.2)) := by
  rw [encLinkRowsProgram_vector]
  simp only [encLinkCoordinateProgram, Program.cutoffLaw, PMF.map_comp, Option.map_map,
    Function.comp_def, encLinkBitAt, encLinkMacLabels, encLinkIndexAt_x, Vector.toList_ofFn]
  rfl

/-- The y rows implement the exact typed coordinate source. -/
theorem encLinkRowsProgram_y (attempts : Nat) (state : SparseOracleFamily)
    (firstKey secondKey : Block) (x y : BitVec coordinateBitCount) (mac : InputMac) :
    (encLinkRowsProgram firstKey secondKey x y (encLinkMacLabels mac) (List.ofFn encLinkYPosition)).cutoffLaw
      (oracleFamilyCutoff attempts) state =
      ((encLinkCoordinateProgram ⟨firstKey, secondKey⟩ .y y mac.y).cutoffLaw
        (oracleFamilyCutoff attempts) state).map (Option.map fun result => (result.1.toList, result.2)) := by
  rw [encLinkRowsProgram_vector]
  simp only [encLinkCoordinateProgram, Program.cutoffLaw, PMF.map_comp, Option.map_map,
    Function.comp_def, encLinkBitAt, encLinkMacLabels, encLinkIndexAt_y, Vector.toList_ofFn]
  rfl

/-- The complete row source retains the exact two-coordinate source order. -/
theorem encLinkRowsProgram_coordinates (attempts : Nat) (state : SparseOracleFamily)
    (firstKey secondKey : Block) (x y : BitVec coordinateBitCount) (mac : InputMac) :
    (encLinkRowsProgram firstKey secondKey x y (encLinkMacLabels mac) (List.finRange 508)).cutoffLaw
      (oracleFamilyCutoff attempts) state =
      bindCutoff ((encLinkCoordinateProgram ⟨firstKey, secondKey⟩ .x x mac.x).cutoffLaw
        (oracleFamilyCutoff attempts) state) (fun result =>
          ((encLinkCoordinateProgram ⟨firstKey, secondKey⟩ .y y mac.y).cutoffLaw
            (oracleFamilyCutoff attempts) result.2).map
              (Option.map fun tail => (result.1.toList ++ tail.1.toList, tail.2))) := by
  rw [encLinkPositions_split, encLinkRowsProgram_append, encLinkRowsProgram_x, bindCutoff_map]
  congr 1
  funext result
  rw [encLinkRowsProgram_y]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
