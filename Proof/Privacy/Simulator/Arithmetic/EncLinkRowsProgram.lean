import Proof.Privacy.Simulator.Arithmetic.EncLinkRowSource
import Proof.Privacy.Simulator.Arithmetic.EncLinkOrder
import Proof.Privacy.Simulator.Arithmetic.ProgramCutoff
import Proof.Privacy.Simulator.Arithmetic.OracleFamilyCutoff

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security.SimulatorMachine Security.OperationalOracle
noncomputable section

/-- The source position selects the same x or y bit as the fixed schedule. -/
def encLinkBitAt (x y : BitVec coordinateBitCount) (position : Fin 508) : Bool :=
  match (encLinkIndexAt position).1 with
  | .x => x.getLsb (encLinkIndexAt position).2
  | .y => y.getLsb (encLinkIndexAt position).2

/-- The source program reads and masks each selected label in its fixed order. -/
def encLinkRowsProgram (firstKey secondKey : Block) (x y : BitVec coordinateBitCount)
    (labels : Fin 508 → Block) : (positions : List (Fin 508)) → Program oracleFamilySpec (List Block) positions.length
  | [] => .pure []
  | position :: positions =>
      .query (.inl (encLinkPhysicalIndex (encLinkIndexAt position),
        .forward (blockFin (xor (encodeBit (encLinkBitAt x y position)) firstKey)))) fun reply =>
        .map (List.cons ((blockFin.symm reply ^^^ secondKey) ^^^ labels position))
          (encLinkRowsProgram firstKey secondKey x y labels positions)

/-- A physical forward request has the exact finite family cutoff law. -/
theorem oracleFamilyCutoff_forward (attempts : Nat) (state : SparseOracleFamily)
    (oracle : Fin 15748) (input : Fin (2 ^ 128)) :
    oracleFamilyCutoff attempts (.inl (oracle, .forward input)) state =
      (drawCutoffLaw attempts ((state.permutations oracle).forward input)).map
        (Option.map fun result => (result.1, state.updatePermutation oracle result.2)) := by
  simp only [oracleFamilyCutoff, oracleFamilyDraw, familyDraw, drawCutoffLaw_map,
    PMF.map_comp, Option.map_map, Function.comp_def, SparseOracleFamily.updatePermutation]

/-- One source row composes its exact masked reply with the remaining source program. -/
theorem encLinkRowsProgram_step (attempts : Nat) (state : SparseOracleFamily)
    (firstKey secondKey : Block) (x y : BitVec coordinateBitCount) (labels : Fin 508 → Block)
    (position : Fin 508) (positions : List (Fin 508)) :
    (encLinkRowsProgram firstKey secondKey x y labels (position :: positions)).cutoffLaw
      (oracleFamilyCutoff attempts) state =
      bindCutoff
        ((drawCutoffLaw attempts ((state.permutations (encLinkPhysicalIndex (encLinkIndexAt position))).forward
          (blockFin (xor (encodeBit (encLinkBitAt x y position)) firstKey)))).map
            (Option.map fun result => encLinkMaskReply secondKey (labels position)
              (result.1, state.updatePermutation (encLinkPhysicalIndex (encLinkIndexAt position)) result.2)))
        (fun result => ((encLinkRowsProgram firstKey secondKey x y labels positions).cutoffLaw
          (oracleFamilyCutoff attempts) result.2).map (Option.map fun tail => (result.1 :: tail.1, tail.2))) := by
  rw [encLinkRowsProgram, Program.cutoffLaw, oracleFamilyCutoff_forward]
  simp only [Program.cutoffLaw, bindCutoff, PMF.bind_map]
  congr 1
  funext result
  cases result <;> rfl

/-- The schedule positions increase by one at every row. -/
def EncLinkConsecutive (position : Nat) (positions : List (Fin 508)) : Prop :=
  ∀ index (inside : index < positions.length), (positions[index]).val = position + index

/-- A nonempty consecutive schedule starts at its declared position. -/
theorem encLinkConsecutive_head (position : Nat) (head : Fin 508) (tail : List (Fin 508))
    (ordered : EncLinkConsecutive position (head :: tail)) : head.val = position := by
  have value := ordered 0 (by simp)
  change head.val = position + 0 at value
  exact value.trans (Nat.add_zero position)

/-- The remaining consecutive schedule starts at the next position. -/
theorem encLinkConsecutive_tail (position : Nat) (head : Fin 508) (tail : List (Fin 508))
    (ordered : EncLinkConsecutive position (head :: tail)) : EncLinkConsecutive (position + 1) tail := by
  intro index inside
  have value := ordered (index + 1) (by simpa using Nat.add_lt_add_right inside 1)
  simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 index] using value

end
end Kriterion.ArgoMAC.ArithmeticSimulator
