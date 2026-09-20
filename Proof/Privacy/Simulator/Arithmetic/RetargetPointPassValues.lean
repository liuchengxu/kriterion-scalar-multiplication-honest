import Proof.Privacy.Simulator.Arithmetic.RetargetPointPassSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling

private theorem privateOffset_sum (pointer : Word) (first second : Nat) :
    pointer + BitVec.ofNat 256 first + BitVec.ofNat 256 second = pointer + BitVec.ofNat 256 (first + second) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- The typed row replacement preserves every other RAM word. -/
theorem pointRowRetargetRam_outside (sample : RowPublicSample) (input : AffineInput) (target : Fin 3 → BaseField)
    (pointer : Word) (row : Fin FieldMacToECMac.outputMacCount) (ram : Word → Word) (address : Word)
    (outside : OutsidePointRow pointer row address) :
    pointRowRetargetRam sample input target pointer row ram address = ram address := by
  simp only [pointRowRetargetRam, Function.update_of_ne outside.2.2,
    Function.update_of_ne outside.2.1, Function.update_of_ne outside.1]

/-- A list of typed replacements preserves each word outside all selected rows. -/
theorem pointRetargetFold_outside (rows : List (Fin FieldMacToECMac.outputMacCount)) (sample : Fin FieldMacToECMac.outputMacCount → RowPublicSample)
    (input : AffineInput) (target : Fin FieldMacToECMac.outputMacCount → Fin 3 → BaseField) (pointer : Word)
    (ram : Word → Word) (address : Word)
    (outside : ∀ row ∈ rows, OutsidePointRow pointer row address) :
    rows.foldl (fun ram row => pointRowRetargetRam (sample row) input (target row) pointer row ram) ram address = ram address := by
  induction rows generalizing ram with
  | nil => rfl
  | cons row rest ih =>
      rw [List.foldl_cons, ih]
      · exact pointRowRetargetRam_outside _ _ _ _ _ _ _ (outside row List.mem_cons_self)
      · intro later member
        exact outside later (List.mem_cons_of_mem _ member)

/-- The three replacement cells contain their exact typed low targets. -/
theorem pointRowRetargetRam_values (sample : RowPublicSample) (input : AffineInput) (target : Fin 3 → BaseField)
    (pointer : Word) (row : Fin FieldMacToECMac.outputMacCount) (ram : Word → Word) :
    let final := pointRowRetargetRam sample input target pointer row ram
    final (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 6105) + 762) =
      BitVec.ofNat 256 ((sample.x.request.retarget input (target 0)).x9Targets 0).val ∧
    final (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 3815) + 508) =
      BitVec.ofNat 256 ((sample.y.request.retarget input (target 1)).x9Targets 0).val ∧
    final (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val) + 1016) =
      BitVec.ofNat 256 ((sample.z.request.retarget input (target 2)).x9Targets 0).val := by
  have distinct (first second : Nat) (a : first < 9158) (b : second < 9158) (different : first ≠ second) :
      pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + first) ≠
        pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + second) := by
    apply privateOffset_ne <;> have bound := row.isLt <;> have rowCount : FieldMacToECMac.outputMacCount = 91 := rfl <;> omega
  have xy := distinct 6867 4323 (by decide) (by decide) (by decide)
  have xz := distinct 6867 1016 (by decide) (by decide) (by decide)
  have yz := distinct 4323 1016 (by decide) (by decide) (by decide)
  have address (first second : Nat) :
      pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + first) + BitVec.ofNat 256 second =
        pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + (first + second)) := by
    rw [privateOffset_sum, Nat.add_assoc]
  have xAddress : pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 6105) + 762 =
      pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 6867) := address 6105 762
  have yAddress : pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 3815) + 508 =
      pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 4323) := address 3815 508
  have zAddress : pointer + BitVec.ofNat 256 (1017 + 9158 * row.val) + 1016 =
      pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 1016) := privateOffset_sum pointer _ 1016
  dsimp only
  simp only [pointRowRetargetRam, xAddress, yAddress, zAddress,
    Function.update_of_ne xy, Function.update_of_ne xz, Function.update_of_ne yz, Function.update_self,
    and_self]

private theorem fold_preserves_value {A : Type} (rows : List A)
    (step : (Word → Word) → A → Word → Word) (ram : Word → Word) (address : Word)
    (preserves : ∀ row ∈ rows, ∀ ram, step ram row address = ram address) :
    rows.foldl step ram address = ram address := by
  induction rows generalizing ram with
  | nil => rfl
  | cons row rest ih =>
      rw [List.foldl_cons, ih]
      · exact preserves row List.mem_cons_self ram
      · intro later member cells
        exact preserves later (List.mem_cons_of_mem _ member) cells

private theorem fold_selected_value {A : Type} [DecidableEq A] (rows : List A) (selected : A)
    (step : (Word → Word) → A → Word → Word) (ram : Word → Word) (address value : Word)
    (unique : rows.Nodup) (member : selected ∈ rows)
    (writes : ∀ ram, step ram selected address = value)
    (preserves : ∀ row ∈ rows, row ≠ selected → ∀ ram, step ram row address = ram address) :
    rows.foldl step ram address = value := by
  induction rows generalizing ram with
  | nil => simp at member
  | cons row rest ih =>
      have distinct := List.nodup_cons.mp unique
      rw [List.foldl_cons]
      by_cases same : row = selected
      · subst row
        rw [fold_preserves_value]
        · exact writes ram
        · intro later member cells
          exact preserves later (List.mem_cons_of_mem _ member)
            (by intro same; exact distinct.1 (same ▸ member)) cells
      · apply ih _ distinct.2 ((List.mem_cons.mp member).resolve_left (Ne.symm same))
        intro later member different cells
        exact preserves later (List.mem_cons_of_mem _ member) different cells

/-- The complete typed pass retains each selected row's replacement value. -/
theorem pointRetargetFold_selected (rows : List (Fin FieldMacToECMac.outputMacCount)) (sample : Fin FieldMacToECMac.outputMacCount → RowPublicSample)
    (input : AffineInput) (target : Fin FieldMacToECMac.outputMacCount → Fin 3 → BaseField) (pointer : Word)
    (ram : Word → Word) (row : Fin FieldMacToECMac.outputMacCount) (offset : Nat) (value : Word)
    (unique : rows.Nodup) (member : row ∈ rows) (inside : offset < 9158)
    (writes : ∀ cells, pointRowRetargetRam (sample row) input (target row) pointer row cells
      (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + offset)) = value) :
    rows.foldl (fun cells row => pointRowRetargetRam (sample row) input (target row) pointer row cells) ram
      (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + offset)) = value := by
  apply fold_selected_value rows row _ ram _ value unique member writes
  intro later present different cells
  exact pointRowRetargetRam_outside _ _ _ _ _ _ _
    (pointRow_otherSource pointer later row offset inside (Ne.symm different))

/-- The full typed pass retains all three selected low targets for every row. -/
theorem pointRetargetFold_values (sample : Fin FieldMacToECMac.outputMacCount → RowPublicSample) (input : AffineInput)
    (target : Fin FieldMacToECMac.outputMacCount → Fin 3 → BaseField) (pointer : Word) (ram : Word → Word) (row : Fin FieldMacToECMac.outputMacCount) :
    let final := (List.finRange FieldMacToECMac.outputMacCount).foldl
      (fun cells row => pointRowRetargetRam (sample row) input (target row) pointer row cells) ram
    final (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 6867)) =
      BitVec.ofNat 256 (((sample row).x.request.retarget input (target row 0)).x9Targets 0).val ∧
    final (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 4323)) =
      BitVec.ofNat 256 (((sample row).y.request.retarget input (target row 1)).x9Targets 0).val ∧
    final (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 1016)) =
      BitVec.ofNat 256 (((sample row).z.request.retarget input (target row 2)).x9Targets 0).val := by
  have address (start offset : Nat) : pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + start) + BitVec.ofNat 256 offset =
      pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + (start + offset)) := by
    rw [privateOffset_sum, Nat.add_assoc]
  have xAddress : pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 6105) + 762 =
      pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 6867) := address 6105 762
  have yAddress : pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 3815) + 508 =
      pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 4323) := address 3815 508
  have zAddress : pointer + BitVec.ofNat 256 (1017 + 9158 * row.val) + 1016 =
      pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + 1016) := privateOffset_sum pointer _ 1016
  have one (offset : Nat) (value : Word) (inside : offset < 9158)
      (writes : ∀ cells, pointRowRetargetRam (sample row) input (target row) pointer row cells
        (pointer + BitVec.ofNat 256 (1017 + 9158 * row.val + offset)) = value) :=
    pointRetargetFold_selected (List.finRange FieldMacToECMac.outputMacCount) sample input target pointer ram row offset value
      (List.nodup_finRange FieldMacToECMac.outputMacCount) (List.mem_finRange row) inside writes
  dsimp only
  refine ⟨one 6867 _ (by decide) ?_, one 4323 _ (by decide) ?_, one 1016 _ (by decide) ?_⟩
  · intro cells
    have values := (pointRowRetargetRam_values (sample row) input (target row) pointer row cells).1
    rw [xAddress] at values
    exact values
  · intro cells
    have values := (pointRowRetargetRam_values (sample row) input (target row) pointer row cells).2.1
    rw [yAddress] at values
    exact values
  · intro cells
    have values := (pointRowRetargetRam_values (sample row) input (target row) pointer row cells).2.2
    rw [zAddress] at values
    exact values

end Kriterion.ArgoMAC.ArithmeticSimulator
