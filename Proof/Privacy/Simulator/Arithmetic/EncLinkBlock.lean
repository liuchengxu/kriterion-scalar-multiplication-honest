import Proof.Privacy.Simulator.Arithmetic.EncLinkCode

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host supplies separate success and cutoff return instructions. -/
def ContainsEncLink (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 7468, pc.val < 7466 → host.code[(labels pc).val] =
    relocate labels ((encLink attempts).code[pc.val]'pc.isLt)

/-- Every linear link block retains its proved host contract. -/
theorem encLinkBlock_linear (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (program : List LinearInstruction) (block : Nat → Fin 7468)
    (contained : ContainsLinear (encLink attempts) program block)
    (inside : ∀ index, index < program.length → (block index).val < 7466) :
    ContainsLinear host program (labels ∘ block) := by
  intro index valid
  exact (present (block index) (inside index valid)).trans
    ((congrArg (relocate labels) (contained index valid)).trans
      (LinearInstruction.relocate_emit labels _ _))

/-- The host contains the internal programmed query body. -/
theorem encLinkBlock_query (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels) :
    ContainsInternalForward host attempts (labels ∘ encLinkQueryLabels) := by
  intro pc valid
  have inside : (encLinkQueryLabels pc).val < 7466 := by
    simp [encLinkQueryLabels, valid]
    omega
  exact (present (encLinkQueryLabels pc) inside).trans
    ((congrArg (relocate labels) (encLink_query attempts pc valid)).trans
      (relocate_comp encLinkQueryLabels labels _))

/-- The host contains the exact hash sampling body. -/
theorem encLinkBlock_hash (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels) :
    ContainsHashHandler host (labels ∘ encLinkHashLabels) := by
  intro pc valid
  have bound : pc.val < 73 := by
    have := pc.isLt
    have : pc.val ≠ 73 := by intro equal; exact valid (Fin.ext equal)
    omega
  have inside : (encLinkHashLabels pc).val < 7466 := by
    simp [encLinkHashLabels, encLinkLabels, bound]
    omega
  exact (present (encLinkHashLabels pc) inside).trans
    ((congrArg (relocate labels) (encLink_hash attempts pc valid)).trans
      (relocate_comp encLinkHashLabels labels _))

/-- The host contains the fourteen-bit fixed-index reader. -/
theorem encLinkBlock_reader (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels) :
    ContainsWordInput host 14 (labels ∘ encLinkReaderLabels) := by
  intro pc valid
  have inside : (encLinkReaderLabels pc).val < 7466 := by
    simp [encLinkReaderLabels, encLinkLabels, valid]
    omega
  exact (present (encLinkReaderLabels pc) inside).trans
    ((congrArg (relocate labels) (encLink_reader attempts pc valid)).trans
      (relocate_comp encLinkReaderLabels labels _))

end Kriterion.ArgoMAC.ArithmeticSimulator
