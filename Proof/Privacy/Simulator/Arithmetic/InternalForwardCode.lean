import Construction.Simulator.InternalForward
import Proof.Privacy.Simulator.Arithmetic.StoredForwardBlock
import Proof.Privacy.Simulator.Arithmetic.OverlayScan

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The internal query contains the stored forward handler. -/
theorem internalForward_stored (attempts : Nat) :
    ContainsStoredForward (internalForward attempts) attempts internalForwardLabels := by
  intro pc valid
  have bound : pc.val < 178 := by
    have := pc.isLt
    have : pc.val ≠ 178 := by intro equal; exact valid (Fin.ext equal)
    omega
  simp [internalForward, internalForwardLabels, bound]
  rfl

/-- The internal query contains the overlay metadata loader. -/
theorem internalForward_loader (attempts : Nat) :
    ContainsLinear (internalForward attempts) overlayLoad internalOverlayLoadLabels := by
  intro index valid
  have bound : index < 5 := valid
  have next : index + 1 ≤ 5 := by omega
  simp only [internalForward, internalOverlayLoadLabels, Vector.getElem_ofFn,
    Nat.min_eq_left (by omega : index ≤ 5),
    show ¬ 179 + index < 178 by omega, dite_false,
    show 179 ≤ 179 + index ∧ 179 + index < 184 by omega, dite_true,
    Nat.add_sub_cancel_left, and_self, ↓reduceDIte]


/-- The internal query contains the complete overlay scan. -/
theorem internalForward_scanner (attempts : Nat) :
    ContainsSwapTable (internalForward attempts) internalOverlayScanLabels := by
  intro pc valid
  have bound : pc.val < 13 := by
    have := pc.isLt
    have : pc.val ≠ 13 := by intro equal; exact valid (Fin.ext equal)
    omega
  simp [internalForward, internalOverlayScanLabels,
    show ¬ 184 + pc.val < 178 by omega,
    show ¬ (179 ≤ 184 + pc.val ∧ 184 + pc.val < 184) by omega,
    show 184 ≤ 184 + pc.val by omega, show 184 + pc.val < 197 by omega]
  rfl

/-- The host supplies two separate continuations for success and cutoff failure. -/
def ContainsInternalForward (host : Machine) (attempts : Nat)
    (labels : Fin 199 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 199, pc.val < 197 → host.code[(labels pc).val] =
    relocate labels ((internalForward attempts).code[pc.val]'pc.isLt)

/-- The host contains the stored query body. -/
theorem internalForwardBlock_stored (host : Machine) (attempts : Nat)
    (labels : Fin 199 → Fin (host.size + 1))
    (present : ContainsInternalForward host attempts labels) :
    ContainsStoredForward host attempts (labels ∘ internalForwardLabels) := by
  intro pc valid
  have bound : pc.val < 178 := by
    have := pc.isLt
    have : pc.val ≠ 178 := by intro equal; exact valid (Fin.ext equal)
    omega
  exact (present (internalForwardLabels pc) (by change pc.val < 197; omega)).trans
    ((congrArg (relocate labels) (internalForward_stored attempts pc valid)).trans
      (relocate_comp internalForwardLabels labels _))

/-- The host contains the overlay loader. -/
theorem internalForwardBlock_loader (host : Machine) (attempts : Nat)
    (labels : Fin 199 → Fin (host.size + 1))
    (present : ContainsInternalForward host attempts labels) :
    ContainsLinear host overlayLoad (labels ∘ internalOverlayLoadLabels) := by
  intro index valid
  have bound : index < 5 := valid
  exact (present (internalOverlayLoadLabels index)
    (by change 179 + min index 5 < 197; omega)).trans
    ((congrArg (relocate labels) (internalForward_loader attempts index valid)).trans
      (LinearInstruction.relocate_emit labels _ _))

/-- The host contains the overlay scan. -/
theorem internalForwardBlock_scanner (host : Machine) (attempts : Nat)
    (labels : Fin 199 → Fin (host.size + 1))
    (present : ContainsInternalForward host attempts labels) :
    ContainsSwapTable host (labels ∘ internalOverlayScanLabels) := by
  intro pc valid
  have bound : pc.val < 13 := by
    have := pc.isLt
    have : pc.val ≠ 13 := by intro equal; exact valid (Fin.ext equal)
    omega
  exact (present (internalOverlayScanLabels pc) (by change 184 + pc.val < 197; omega)).trans
    ((congrArg (relocate labels) (internalForward_scanner attempts pc valid)).trans
      (relocate_comp internalOverlayScanLabels labels _))

end Kriterion.ArgoMAC.ArithmeticSimulator
