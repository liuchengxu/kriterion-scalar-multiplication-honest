import Proof.Privacy.Simulator.Arithmetic.EncLinkIndex
import Proof.Privacy.Simulator.Arithmetic.InternalForwardFamily

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Every EncPRF index selects a permutation before the hash region. -/
theorem encLinkIndexValue_permutation (index : EncPRF.PermutationIndex) :
    encLinkIndexValue index < 15748 := by
  have bound := (Fintype.equivFin EncPRF.PermutationIndex index).isLt
  have small : (Fintype.equivFin EncPRF.PermutationIndex index).val < 508 := by
    simpa only [encPermutationIndex_count] using bound
  unfold encLinkIndexValue
  omega

/-- The physical index uses the canonical public protocol encoding. -/
noncomputable def encLinkPhysicalIndex (index : EncPRF.PermutationIndex) : Fin 15748 :=
  ⟨encLinkIndexValue index, encLinkIndexValue_permutation index⟩

/-- Different source indices select different physical permutations. -/
theorem encLinkPhysicalIndex_injective : Function.Injective encLinkPhysicalIndex := by
  intro first second equal
  apply (Fintype.equivFin EncPRF.PermutationIndex).injective
  apply Fin.ext
  have values := congrArg Fin.val equal
  change (Fintype.equivFin EncPRF.PermutationIndex first).val + 15240 =
    (Fintype.equivFin EncPRF.PermutationIndex second).val + 15240 at values
  omega

/-- The full schedule queries each physical permutation at most once. -/
theorem encLinkIndices_nodup : encLinkIndices.Nodup := by
  unfold encLinkIndices
  apply List.nodup_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · exact (List.nodup_finRange _).map (fun _ _ equal => Prod.mk.inj equal |>.2)
  · exact (List.nodup_finRange _).map (fun _ _ equal => Prod.mk.inj equal |>.2)
  · intro index left other right equal
    obtain ⟨first, _, equalFirst⟩ := List.mem_map.mp left
    obtain ⟨second, _, equalSecond⟩ := List.mem_map.mp right
    have impossible := congrArg Prod.fst (equalFirst.trans (equal.trans equalSecond.symm))
    cases impossible

/-- The encoded schedule also has no repeated physical permutation. -/
theorem encLinkPhysicalIndices_nodup :
    (encLinkIndices.map encLinkPhysicalIndex).Nodup :=
  encLinkIndices_nodup.map encLinkPhysicalIndex_injective

end Kriterion.ArgoMAC.ArithmeticSimulator
