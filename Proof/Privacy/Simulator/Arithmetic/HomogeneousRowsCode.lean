import Proof.Privacy.Simulator.Arithmetic.HomogeneousRowsMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each row boundary names its point-load entry or the caller return. -/
def homogeneousRowBoundary {count : Nat} (index : Nat) (inside : index ≤ count + 1) : Fin (25 * (count + 1) + 2) :=
  ⟨1 + 25 * index, by omega⟩

/-- Each row slot names one fixed instruction. -/
def homogeneousRowSlot {count : Nat} (index : Fin (count + 1)) (offset : Fin 25) : Fin (25 * (count + 1) + 2) :=
  ⟨1 + 25 * index.val + offset.val, by have i := index.isLt; have o := offset.isLt; omega⟩

/-- The host contains every homogeneous-row instruction before the return. -/
def ContainsHomogeneousRows (host : Machine) (count : Nat) (fits : 25 * (count + 1) + 1 < 2 ^ 256)
    (labels : Fin (25 * (count + 1) + 2) → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin (25 * (count + 1) + 2), pc.val < 25 * (count + 1) + 1 →
    host.code[(labels pc).val] = relocate labels ((homogeneousRows count fits).code[pc.val])

/-- Every row contains the fixed homogeneous conversion block. -/
theorem homogeneousRowBlock_conversion (host : Machine) (count : Nat) (fits : 25 * (count + 1) + 1 < 2 ^ 256)
    (labels : Fin (25 * (count + 1) + 2) → Fin (host.size + 1))
    (present : ContainsHomogeneousRows host count fits labels) (index : Fin (count + 1)) :
    ContainsHomogeneousPoint host (labels ∘ homogeneousRowLabels index) := by
  intro pc inside
  have i := index.isLt
  have position : 1 + 25 * index.val + 10 + pc.val < 25 * (count + 1) + 1 := by omega
  have quotient : (1 + 25 * index.val + 10 + pc.val - 1) / 25 = index.val := by omega
  have remainder : (1 + 25 * index.val + 10 + pc.val - 1) % 25 = 10 + pc.val := by omega
  have source : (homogeneousRows count fits).code[(homogeneousRowLabels index pc).val] =
      relocate (homogeneousRowLabels index) (homogeneousPoint.code[pc.val]'(by exact pc.isLt)) := by
    simp only [homogeneousRows, Vector.getElem_ofFn, homogeneousRowLabels]
    rw [dif_neg (by omega : 1 + 25 * index.val + 10 + pc.val ≠ 0), dif_pos position]
    simp only [quotient, remainder]
    simp [show 10 + pc.val ≠ 0 by omega, show 10 + pc.val ≠ 1 by omega, show 10 + pc.val ≠ 2 by omega,
      show 10 + pc.val ≠ 3 by omega, show 10 + pc.val ≠ 4 by omega, show 10 + pc.val ≠ 5 by omega,
      show 10 + pc.val ≠ 6 by omega, show 10 + pc.val ≠ 7 by omega, show 10 + pc.val ≠ 8 by omega,
      show 10 + pc.val ≠ 9 by omega, show 10 + pc.val < 18 by omega]
    rfl
  exact ((present (homogeneousRowLabels index pc) position).trans (congrArg (relocate labels) source)).trans
    (relocate_comp (homogeneousRowLabels index) labels _)

/-- The host contains the fixed point and scale load instructions. -/
theorem homogeneousRowBlock_load_code (host : Machine) (count : Nat) (fits : 25 * (count + 1) + 1 < 2 ^ 256)
    (labels : Fin (25 * (count + 1) + 2) → Fin (host.size + 1))
    (present : ContainsHomogeneousRows host count fits labels) (index : Fin (count + 1)) (offset : Fin 25) (upper : offset.val < 10) :
    host.code[(labels (homogeneousRowSlot index offset)).val] = relocate labels
      (if offset.val = 0 then .constant 8 (BitVec.ofNat 256 (3 * (index.val - 1))) (homogeneousRowSlot index 1)
      else if offset.val = 1 then .arithmetic .add 8 10 8 (homogeneousRowSlot index 2)
      else if offset.val = 2 then .load 2 8 (homogeneousRowSlot index 3)
      else if offset.val = 3 then .arithmetic .add 8 8 12 (homogeneousRowSlot index 4)
      else if offset.val = 4 then .load 3 8 (homogeneousRowSlot index 5)
      else if offset.val = 5 then .arithmetic .add 8 8 12 (homogeneousRowSlot index 6)
      else if offset.val = 6 then .load 4 8 (homogeneousRowSlot index 7)
      else if offset.val = 7 then .constant 8 (BitVec.ofNat 256 index.val) (homogeneousRowSlot index 8)
      else if offset.val = 8 then .arithmetic .add 8 11 8 (homogeneousRowSlot index 9)
      else .load 0 8 (homogeneousRowSlot index 10)) := by
  have i := index.isLt
  have position : 1 + 25 * index.val + offset.val < 25 * (count + 1) + 1 := by omega
  have quotient : (1 + 25 * index.val + offset.val - 1) / 25 = index.val := by omega
  have remainder : (1 + 25 * index.val + offset.val - 1) % 25 = offset.val := by omega
  rw [present (homogeneousRowSlot index offset) position]
  apply congrArg (relocate labels)
  simp only [homogeneousRows, Vector.getElem_ofFn, homogeneousRowSlot]
  rw [dif_neg (by omega : 1 + 25 * index.val + offset.val ≠ 0), dif_pos position]
  simp only [quotient, remainder]
  by_cases h0 : offset.val = 0
  · simp [h0]
  by_cases h1 : offset.val = 1
  · simp [h1]
  by_cases h2 : offset.val = 2
  · simp [h2]
  by_cases h3 : offset.val = 3
  · simp [h3]
  by_cases h4 : offset.val = 4
  · simp [h4]
  by_cases h5 : offset.val = 5
  · simp [h5]
  by_cases h6 : offset.val = 6
  · simp [h6]
  by_cases h7 : offset.val = 7
  · simp [h7]
  by_cases h8 : offset.val = 8
  · simp [h8]
  have h9 : offset.val = 9 := by omega
  simp [h9]

/-- The host contains the fixed homogeneous coordinate stores. -/
theorem homogeneousRowBlock_store_code (host : Machine) (count : Nat) (fits : 25 * (count + 1) + 1 < 2 ^ 256)
    (labels : Fin (25 * (count + 1) + 2) → Fin (host.size + 1))
    (present : ContainsHomogeneousRows host count fits labels) (index : Fin (count + 1)) (offset : Fin 25) (lower : 18 ≤ offset.val) :
    host.code[(labels (homogeneousRowSlot index offset)).val] = relocate labels
      (if offset.val = 18 then .constant 8 (BitVec.ofNat 256 (3 * index.val)) (homogeneousRowSlot index 19)
      else if offset.val = 19 then .arithmetic .add 8 13 8 (homogeneousRowSlot index 20)
      else if offset.val = 20 then .store 8 5 (homogeneousRowSlot index 21)
      else if offset.val = 21 then .arithmetic .add 8 8 12 (homogeneousRowSlot index 22)
      else if offset.val = 22 then .store 8 6 (homogeneousRowSlot index 23)
      else if offset.val = 23 then .arithmetic .add 8 8 12 (homogeneousRowSlot index 24)
      else .store 8 7 (homogeneousRowBoundary (index.val + 1) index.isLt)) := by
  have i := index.isLt
  have o := offset.isLt
  have position : 1 + 25 * index.val + offset.val < 25 * (count + 1) + 1 := by omega
  have quotient : (1 + 25 * index.val + offset.val - 1) / 25 = index.val := by omega
  have remainder : (1 + 25 * index.val + offset.val - 1) % 25 = offset.val := by omega
  rw [present (homogeneousRowSlot index offset) position]
  apply congrArg (relocate labels)
  simp [homogeneousRows, homogeneousRowSlot, homogeneousRowBoundary, position,
    show 1 + 25 * index.val + offset.val ≤ 25 * (count + 1) by omega, quotient, remainder,
    show offset.val ≠ 0 by omega, show offset.val ≠ 1 by omega, show offset.val ≠ 2 by omega,
    show offset.val ≠ 3 by omega, show offset.val ≠ 4 by omega, show offset.val ≠ 5 by omega,
    show offset.val ≠ 6 by omega, show offset.val ≠ 7 by omega, show offset.val ≠ 8 by omega,
    show offset.val ≠ 9 by omega, show ¬offset.val < 18 by omega]

end Kriterion.ArgoMAC.ArithmeticSimulator
