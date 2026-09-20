import Proof.Privacy.Simulator.Arithmetic.EncLinkLoop

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The caller receives the actual loop label, memory, and accumulated instruction charge. -/
noncomputable def encLinkContinue [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 7468 → Fin (host.size + 1)) (reserve : Nat) (result : EncLinkResult) :
    PMF (Option (Configuration (host.size + 1) × Nat)) :=
  (run host (reserve - result.1.2.1) ⟨labels result.1.2.2, result.1.1⟩).map
    (Option.map fun final => (final.1, final.2 + result.1.2.1))

/-- The accumulated row charge distributes over the complete remaining loop source. -/
theorem encLinkCharge_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 7468 → Fin (host.size + 1)) (source : PMF EncLinkResult) (cost reserve : Nat) :
    (source.bind (encLinkContinue host labels reserve)).map
      (Option.map fun final => (final.1, final.2 + cost)) =
      (source.map (encLinkCharge cost)).bind (encLinkContinue host labels (cost + reserve)) := by
  unfold encLinkContinue
  have charged := chargedContinuation host labels (source.map Prod.fst) cost reserve
  simpa only [encLinkContinue, PMF.bind_map, PMF.map_comp, Function.comp_def, encLinkCharge] using charged

/-- The exact row reserve is below the common allowance for the remaining loop. -/
theorem encLinkInvariant_reserve (attempts : Nat) (state : SparseOracleFamily) (memory : Memory)
    (index : EncPRF.PermutationIndex) (indices : List EncPRF.PermutationIndex) (suffix : List Bool)
    (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit) :
    encLinkIterationReserve attempts (state.permutations (encLinkPhysicalIndex index)).base.used
      (state.permutations (encLinkPhysicalIndex index)).overlay.length 0 memory index
      (indices.flatMap encLinkIndexBits ++ suffix) ≤ encLinkRowBudget attempts (limit + indices.length + 1) := by
  have bound := encLinkIterationReserve_bound attempts
    (state.permutations (encLinkPhysicalIndex index)).base.used
    (state.permutations (encLinkPhysicalIndex index)).overlay.length 0 memory index
    (indices.flatMap encLinkIndexBits ++ suffix)
  have base := ready.baseCount (encLinkPhysicalIndex index)
  have overlay := ready.overlayCount (encLinkPhysicalIndex index)
  unfold encLinkRowBudget
  omega

/-- The row law permits any larger caller reserve. -/
theorem encLinkBlock_readyBudget [BN254.FieldCertificate] (host : Machine) (attempts reserve : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (state : SparseOracleFamily) (memory : Memory) (index : EncPRF.PermutationIndex)
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (attemptFits : attempts < 2 ^ 256)
    (enough : encLinkRowBudget attempts (limit + indices.length + 1) ≤ reserve) :
    run host reserve ⟨labels 7208, memory⟩ =
      (encLinkRowSamples attempts state memory index (indices.flatMap encLinkIndexBits ++ suffix)
        (encLinkInput memory firstKey)).bind (encLinkContinue host labels reserve) := by
  let needed := encLinkIterationReserve attempts (state.permutations (encLinkPhysicalIndex index)).base.used
    (state.permutations (encLinkPhysicalIndex index)).overlay.length 0 memory index
    (indices.flatMap encLinkIndexBits ++ suffix)
  have bound : needed ≤ reserve := le_trans (encLinkInvariant_reserve attempts state memory index indices
    suffix firstKey output limit ready) enough
  have law := encLinkBlock_ready host attempts (reserve - needed) labels present state memory index indices
    suffix firstKey output limit ready attemptFits
  dsimp only at law
  have same : encLinkIterationReserve attempts (state.permutations (encLinkPhysicalIndex index)).base.used
      (state.permutations (encLinkPhysicalIndex index)).overlay.length (reserve - needed) memory index
      (indices.flatMap encLinkIndexBits ++ suffix) = reserve := by
    dsimp [needed, encLinkIterationReserve, internalForwardReserve] at bound ⊢
    omega
  unfold encLinkContinue
  simpa only [same] using law

end Kriterion.ArgoMAC.ArithmeticSimulator
