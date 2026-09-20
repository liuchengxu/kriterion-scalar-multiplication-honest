import Proof.Privacy.Simulator.Arithmetic.RetargetPointRowSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling
attribute [local irreducible] retargetPointRow

/-- The source row replaces only the three selected low targets. -/
def pointRowRetargetRam (sample : RowPublicSample) (input : AffineInput) (target : Fin 3 → BaseField)
    (pointer : Word) (row : Fin FieldMacToECMac.outputMacCount) (ram : Word → Word) : Word → Word :=
  Function.update
    (Function.update
      (Function.update ram (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 6105) + 762)
        (BitVec.ofNat 256 ((sample.x.request.retarget input (target 0)).x9Targets 0).val))
      (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 3815) + 508)
      (BitVec.ofNat 256 ((sample.y.request.retarget input (target 1)).x9Targets 0).val))
    (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val) + 1016)
    (BitVec.ofNat 256 ((sample.z.request.retarget input (target 2)).x9Targets 0).val)

/-- A row update preserves every word of each other source row. -/
theorem pointRow_otherSource (pointer : Word) (written source : Fin FieldMacToECMac.outputMacCount) (offset : Nat)
    (inside : offset < 9158) (different : source ≠ written) :
    OutsidePointRow pointer written (pointer + BitVec.ofNat 256 (1017 + 9158 * source.val + offset)) := by
  have distinct : source.val ≠ written.val := fun same => different (Fin.ext same)
  have sourceBound := source.isLt
  have writtenBound := written.isLt
  have rowCount : FieldMacToECMac.outputMacCount = 91 := rfl
  refine ⟨?_, ?_, ?_⟩
  · apply privateOffset_add_ne _ _ _ 762 <;> omega
  · apply privateOffset_add_ne _ _ _ 508 <;> omega
  · apply privateOffset_add_ne _ _ _ 1016 <;> omega

/-- A distinct row list implements the exact sequence of typed low-target replacements. -/
theorem retargetPointRows_ram (rows : List (Fin FieldMacToECMac.outputMacCount)) (sample : Fin FieldMacToECMac.outputMacCount → RowPublicSample)
    (input : AffineInput) (memory : Memory) (target : Fin FieldMacToECMac.outputMacCount → Fin 3 → BaseField)
    (unique : rows.Nodup)
    (stored : ∀ row ∈ rows, WordsAt memory.ram (memory.registers 11)
      (1017 + 9158 * row.val) (rowSchedule.words (sample row)))
    (encoded : ∀ factor, memory.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (polynomialInput input factor).val)
    (requested : ∀ row ∈ rows, ∀ coordinate : Fin 3,
      memory.ram (memory.registers 14 + BitVec.ofNat 256 (3 * row.val + coordinate.val)) = BitVec.ofNat 256 (target row coordinate).val)
    (separate : ∀ source ∈ rows, ∀ written ∈ rows, ∀ coordinate : Fin 3,
      OutsidePointRow (memory.registers 11) written
        (memory.registers 14 + BitVec.ofNat 256 (3 * source.val + coordinate.val))) :
    (executeLinear (rows.flatMap retargetPointRow) memory).ram =
      rows.foldl (fun ram row => pointRowRetargetRam (sample row) input (target row) (memory.registers 11) row ram) memory.ram := by
  induction rows generalizing memory with
  | nil => rfl
  | cons row rest ih =>
      have noDuplicates := List.nodup_cons.mp unique
      let next := executeLinear (retargetPointRow row) memory
      have saved := retargetPointRow_preserves row memory
      have sourcePointer : next.registers 11 = memory.registers 11 := saved.2 11 (by decide) (by decide) (by decide)
      have targetPointer : next.registers 14 = memory.registers 14 := saved.2 14 (by decide) (by decide) (by decide)
      have nextStored : ∀ later ∈ rest, WordsAt next.ram (next.registers 11)
          (1017 + 9158 * later.val) (rowSchedule.words (sample later)) := by
        intro later member index inside
        rw [sourcePointer, retargetPointRow_outside]
        · exact stored later (List.mem_cons_of_mem _ member) index inside
        · apply pointRow_otherSource
          · rw [rowSchedule.wordsLength] at inside
            exact inside
          · intro same
            exact noDuplicates.1 (same ▸ member)
      have nextFactors : ∀ factor, next.registers (polynomialFactorRegister factor) =
          BitVec.ofNat 256 (polynomialInput input factor).val := by
        intro factor
        have bounds : 5 ≤ (polynomialFactorRegister factor).val ∧
            polynomialFactorRegister factor ≠ 10 ∧ polynomialFactorRegister factor ≠ 13 := by
          fin_cases factor <;> decide
        exact (saved.2 _ bounds.1 bounds.2.1 bounds.2.2).trans (encoded factor)
      have nextRequested : ∀ later ∈ rest, ∀ coordinate : Fin 3,
          next.ram (next.registers 14 + BitVec.ofNat 256 (3 * later.val + coordinate.val)) =
            BitVec.ofNat 256 (target later coordinate).val := by
        intro later member coordinate
        rw [targetPointer, retargetPointRow_outside]
        · exact requested later (List.mem_cons_of_mem _ member) coordinate
        · exact separate later (List.mem_cons_of_mem _ member) row List.mem_cons_self coordinate
      have nextSeparate : ∀ source ∈ rest, ∀ written ∈ rest, ∀ coordinate : Fin 3,
          OutsidePointRow (next.registers 11) written
            (next.registers 14 + BitVec.ofNat 256 (3 * source.val + coordinate.val)) := by
        intro source first written second coordinate
        rw [sourcePointer, targetPointer]
        exact separate source (List.mem_cons_of_mem _ first) written (List.mem_cons_of_mem _ second) coordinate
      have after := ih next noDuplicates.2 nextStored nextFactors nextRequested nextSeparate
      have first : next.ram = pointRowRetargetRam (sample row) input (target row) (memory.registers 11) row memory.ram :=
        retargetPointRow_ram row (sample row) input memory (target row)
          (stored row List.mem_cons_self) encoded (requested row List.mem_cons_self)
          (separate row List.mem_cons_self row List.mem_cons_self)
      simp only [List.flatMap_cons, executeLinear_append, List.foldl_cons]
      change (executeLinear (rest.flatMap retargetPointRow) next).ram = _
      rw [after, sourcePointer, first]

/-- The complete point pass matches all 273 typed source replacements. -/
theorem retargetPointCode_ram (sample : Fin FieldMacToECMac.outputMacCount → RowPublicSample) (input : AffineInput)
    (memory : Memory) (target : Fin FieldMacToECMac.outputMacCount → Fin 3 → BaseField)
    (stored : ∀ row, WordsAt memory.ram (memory.registers 11)
      (1017 + 9158 * row.val) (rowSchedule.words (sample row)))
    (coordinates : memory.ram (memory.registers 12) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (memory.registers 12 + 1) = BitVec.ofNat 256 input.y.val)
    (requested : ∀ row coordinate,
      memory.ram (memory.registers 14 + BitVec.ofNat 256 (3 * row.val + coordinate.val)) = BitVec.ofNat 256 (target row coordinate).val)
    (separate : ∀ (source written : Fin FieldMacToECMac.outputMacCount) (coordinate : Fin 3), OutsidePointRow (memory.registers 11) written
      (memory.registers 14 + BitVec.ofNat 256 (3 * source.val + coordinate.val))) :
    (executeLinear retargetPointCode memory).ram =
      (List.finRange FieldMacToECMac.outputMacCount).foldl (fun ram row => pointRowRetargetRam (sample row) input (target row)
        (memory.registers 11) row ram) memory.ram := by
  let loaded := executeLinear retargetInput memory
  have saved := retargetInput_preserves memory
  have sourcePointer := saved.2.2 11 (by decide)
  have targetPointer := saved.2.2 14 (by decide)
  rw [retargetPointCode_rows, executeLinear_append]
  have result := retargetPointRows_ram (List.finRange FieldMacToECMac.outputMacCount) sample input loaded target
    (List.nodup_finRange FieldMacToECMac.outputMacCount)
    (by intro row member; rw [saved.1, sourcePointer]; exact stored row)
    (retargetInput_values memory input coordinates)
    (by intro row member coordinate; rw [saved.1, targetPointer]; exact requested row coordinate)
    (by intro source first written second coordinate; rw [sourcePointer, targetPointer]; exact separate source written coordinate)
  simpa only [loaded, saved.1, sourcePointer] using result

end Kriterion.ArgoMAC.ArithmeticSimulator
