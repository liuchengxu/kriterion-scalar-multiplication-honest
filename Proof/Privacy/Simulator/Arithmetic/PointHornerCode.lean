import Proof.Privacy.Simulator.Arithmetic.PointHornerMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each boundary names the next reverse-order Horner entry or its return. -/
def hornerBoundary {count : Nat} (index : Nat) (inside : index ≤ count) : Fin (22 * count + 6) :=
  ⟨5 + 22 * index, by omega⟩

/-- A host contains every Horner instruction before the return. -/
def ContainsPointHorner (host : Machine) (count : Nat) (fits : 22 * count + 5 < 2 ^ 256)
    (labels : Fin (22 * count + 6) → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin (22 * count + 6), pc.val < 22 * count + 5 →
    host.code[(labels pc).val] = relocate labels ((pointHornerMachine count fits).code[pc.val])

/-- Each Horner entry contains the fixed scalar multiplication block. -/
theorem hornerBlock_scalar (host : Machine) (count : Nat) (fits : 22 * count + 5 < 2 ^ 256)
    (labels : Fin (22 * count + 6) → Fin (host.size + 1))
    (present : ContainsPointHorner host count fits labels) (index : Fin count) :
    ContainsScalarMul host (labels ∘ hornerScalarLabels index) := by
  intro pc inside
  have i := index.isLt
  have p := pc.isLt
  have position : 5 + 22 * index.val + 1 + pc.val < 22 * count + 5 := by omega
  have lower : 5 ≤ 5 + 22 * index.val + 1 + pc.val := by omega
  have quotient : (5 + 22 * index.val + 1 + pc.val - 5) / 22 = index.val := by omega
  have remainder : (5 + 22 * index.val + 1 + pc.val - 5) % 22 = pc.val + 1 := by omega
  have source : (pointHornerMachine count fits).code[(hornerScalarLabels index pc).val] =
      relocate (hornerScalarLabels index) (scalarMul.code[pc.val]'(by exact pc.isLt)) := by
    simp [pointHornerMachine, hornerScalarLabels, position, quotient, remainder,
      show 5 + 22 * index.val + 1 + pc.val ≠ 0 by omega,
      show 5 + 22 * index.val + 1 + pc.val ≠ 1 by omega,
      show 5 + 22 * index.val + 1 + pc.val ≠ 2 by omega,
      show 5 + 22 * index.val + 1 + pc.val ≠ 3 by omega,
      show 5 + 22 * index.val + 1 + pc.val ≠ 4 by omega,
      show pc.val + 1 ≠ 0 by omega, show pc.val + 1 < 11 by omega]
    rfl
  exact ((present (hornerScalarLabels index pc) position).trans (congrArg (relocate labels) source)).trans
    (relocate_comp (hornerScalarLabels index) labels _)

/-- Each local slot has a fixed arithmetic instruction. -/
def hornerSlot {count : Nat} (index : Fin count) (offset : Fin 22) : Fin (22 * count + 6) :=
  ⟨5 + 22 * index.val + offset.val, by have i := index.isLt; have o := offset.isLt; omega⟩

/-- The host contains the point-load, addition, and copy tail. -/
theorem hornerBlock_tail_code (host : Machine) (count : Nat) (fits : 22 * count + 5 < 2 ^ 256)
    (labels : Fin (22 * count + 6) → Fin (host.size + 1))
    (present : ContainsPointHorner host count fits labels) (index : Fin count) (offset : Fin 22) (lower : 11 ≤ offset.val) :
    host.code[(labels (hornerSlot index offset)).val] = relocate labels
      (if offset.val = 11 then .constant 8 (BitVec.ofNat 256 (3 * (count - 1 - index.val))) (hornerSlot index 12)
      else if offset.val = 12 then .arithmetic .add 8 10 8 (hornerSlot index 13)
      else if offset.val = 13 then .load 5 8 (hornerSlot index 14)
      else if offset.val = 14 then .arithmetic .add 8 8 12 (hornerSlot index 15)
      else if offset.val = 15 then .load 6 8 (hornerSlot index 16)
      else if offset.val = 16 then .arithmetic .add 8 8 12 (hornerSlot index 17)
      else if offset.val = 17 then .load 7 8 (hornerSlot index 18)
      else if offset.val = 18 then .pointAdd scalarAccumulator scalarAccumulator scalarMultiple (hornerSlot index 19)
      else if offset.val = 19 then .arithmetic .add 5 2 9 (hornerSlot index 20)
      else if offset.val = 20 then .arithmetic .add 6 3 9 (hornerSlot index 21)
      else .arithmetic .add 7 4 9 (hornerBoundary (index.val + 1) index.isLt)) := by
  have i := index.isLt
  have o := offset.isLt
  have position : 5 + 22 * index.val + offset.val < 22 * count + 5 := by omega
  have quotient : (5 + 22 * index.val + offset.val - 5) / 22 = index.val := by omega
  have remainder : (5 + 22 * index.val + offset.val - 5) % 22 = offset.val := by omega
  rw [present (hornerSlot index offset) position]
  apply congrArg (relocate labels)
  simp [pointHornerMachine, hornerSlot, hornerBoundary, position, quotient, remainder,
    show 5 + 22 * index.val + offset.val ≠ 0 by omega,
    show 5 + 22 * index.val + offset.val ≠ 1 by omega,
    show 5 + 22 * index.val + offset.val ≠ 2 by omega,
    show 5 + 22 * index.val + offset.val ≠ 3 by omega,
    show 5 + 22 * index.val + offset.val ≠ 4 by omega,
    show offset.val ≠ 0 by omega, show ¬offset.val < 11 by omega]

end Kriterion.ArgoMAC.ArithmeticSimulator
