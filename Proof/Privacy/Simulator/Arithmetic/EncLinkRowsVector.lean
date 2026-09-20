import Proof.Privacy.Simulator.Arithmetic.EncLinkRowsProgram
import Proof.Privacy.Simulator.Arithmetic.EncLinkProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security.SimulatorMachine
noncomputable section

/-- The optional source map preserves the next cutoff continuation. -/
theorem bindCutoff_map {A B C : Type} (source : PMF (Option A)) (convert : A → B)
    (next : B → PMF (Option C)) :
    bindCutoff (source.map (Option.map convert)) next = bindCutoff source (fun value => next (convert value)) := by
  simp only [bindCutoff, PMF.bind_map, Function.comp_def]
  congr 1
  funext result
  cases result <;> rfl

/-- A final optional map commutes with a cutoff continuation. -/
theorem map_bindCutoff {A B C : Type} (source : PMF (Option A)) (next : A → PMF (Option B))
    (convert : B → C) :
    (bindCutoff source next).map (Option.map convert) =
      bindCutoff source (fun value => (next value).map (Option.map convert)) := by
  simp only [bindCutoff, PMF.map_bind]
  congr 1
  funext result
  cases result <;> simp only [PMF.pure_map, Option.map_none]

/-- The row list preserves the exact finite vector source and each selected label mask. -/
theorem encLinkRowsProgram_vector (attempts : Nat) (state : SparseOracleFamily)
    (firstKey secondKey : Block) (x y : BitVec coordinateBitCount) (labels : Fin 508 → Block)
    (count : Nat) (positions : Fin count → Fin 508) :
    (encLinkRowsProgram firstKey secondKey x y labels (List.ofFn positions)).cutoffLaw
      (oracleFamilyCutoff attempts) state =
      ((encLinkVectorProgram count (fun index => encLinkIndexAt (positions index))
        (fun index => xor (encodeBit (encLinkBitAt x y (positions index))) firstKey)).cutoffLaw
          (oracleFamilyCutoff attempts) state).map (Option.map fun result =>
            (List.ofFn (fun index => (result.1 index ^^^ secondKey) ^^^ labels (positions index)), result.2)) := by
  induction count generalizing state with
  | zero =>
      have empty : List.ofFn positions = [] := List.ofFn_zero
      rw [empty]
      simp only [encLinkRowsProgram, encLinkVectorProgram, Program.cutoffLaw, PMF.pure_map, Option.map_some, List.ofFn_zero]
  | succ count ih =>
      rw [List.ofFn_succ]
      simp only [encLinkRowsProgram, encLinkVectorProgram, Program.cutoffLaw]
      rw [map_bindCutoff]
      congr 1
      funext result
      rw [ih]
      simp only [PMF.map_comp, Option.map_map, Function.comp_def]
      congr 1
      funext tail
      cases tail with
      | none => rfl
      | some tail => simp only [Option.map_some, List.ofFn_succ, Fin.cases_zero, Fin.cases_succ]

/-- Appended row schedules preserve the exact cutoff sequence. -/
theorem encLinkRowsProgram_append (attempts : Nat) (state : SparseOracleFamily)
    (firstKey secondKey : Block) (x y : BitVec coordinateBitCount) (labels : Fin 508 → Block)
    (first second : List (Fin 508)) :
    (encLinkRowsProgram firstKey secondKey x y labels (first ++ second)).cutoffLaw
      (oracleFamilyCutoff attempts) state =
      bindCutoff ((encLinkRowsProgram firstKey secondKey x y labels first).cutoffLaw
        (oracleFamilyCutoff attempts) state) (fun result =>
          ((encLinkRowsProgram firstKey secondKey x y labels second).cutoffLaw
            (oracleFamilyCutoff attempts) result.2).map
              (Option.map fun tail => (result.1 ++ tail.1, tail.2))) := by
  induction first generalizing state with
  | nil =>
      simp only [List.nil_append, encLinkRowsProgram, Program.cutoffLaw, bindCutoff,
      PMF.pure_bind, List.nil_append, Prod.eta]
      change _ = PMF.map (Option.map id) _
      rw [Option.map_id, PMF.map_id]
  | cons head first ih =>
      simp only [List.cons_append, encLinkRowsProgram, Program.cutoffLaw, ih]
      rw [bindCutoff_assoc]
      congr 1
      funext result
      rw [map_bindCutoff, bindCutoff_map]
      congr 1
      funext tail
      simp only [PMF.map_comp, Option.map_map, Function.comp_def, List.cons_append]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
