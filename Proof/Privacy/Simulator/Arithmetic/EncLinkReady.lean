import Proof.Privacy.Simulator.Arithmetic.EncLinkProgress
import Proof.Privacy.Simulator.Arithmetic.EncLinkCost

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The loop invariant supplies every count and frame condition for its actual machine row. -/
theorem encLinkInvariant_conditions (attempts : Nat) (state : SparseOracleFamily) (memory : Memory)
    (index : EncPRF.PermutationIndex) (indices : List EncPRF.PermutationIndex) (suffix : List Bool)
    (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit) :
    let oracle := encLinkPhysicalIndex index
    let prepared := encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix)
    (state.permutations oracle).base.used < 2 ^ 256 ∧
    (state.permutations oracle).overlay.length < 2 ^ 256 ∧
    (oracleLoaded prepared).registers 0 = BitVec.ofNat 256 (state.permutations oracle).base.used ∧
    ∀ result ∈ (storedForwardSamples attempts (state.permutations oracle).base.used prepared).support,
      result.1.ram (overlayHeader result.1) = BitVec.ofNat 256 (state.permutations oracle).overlay.length := by
  let oracle := encLinkPhysicalIndex index
  let prepared := encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix)
  have represented := (encLinkPrepared_family memory index (indices.flatMap encLinkIndexBits ++ suffix) state ready.represented ready.capacity).permutations oracle
  have physical : prepared.registers 9 = BitVec.ofNat 256 oracle.val :=
    (encLinkPrepared_values memory index (indices.flatMap encLinkIndexBits ++ suffix)).2.1
  have room := encLinkInvariant_room state memory index indices suffix firstKey output limit ready
  have capacity := ready.capacity.overlay oracle
  have fit : 2 * ((state.permutations oracle).base.used + 1) ≤ 2 ^ 110 := by
    dsimp only [oracle]; omega
  dsimp only [oracle] at capacity
  refine ⟨by omega, by omega, ?_, ?_⟩
  · exact (oracleLoaded_used prepared oracle.castSucc physical).trans represented.base.count
  · intro result supported
    exact storedForwardSamples_overlayCount attempts _ prepared result.1 result.2 supported oracle.castSucc
      (state.permutations oracle).overlay physical represented.base.count represented.overlay fit

/-- The concrete loop invariant gives the complete row law without extra callback assumptions. -/
theorem encLinkBlock_ready [BN254.FieldCertificate] (host : Machine) (attempts fuel : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (state : SparseOracleFamily) (memory : Memory) (index : EncPRF.PermutationIndex)
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (attemptFits : attempts < 2 ^ 256) :
    let oracle := encLinkPhysicalIndex index
    let rest := indices.flatMap encLinkIndexBits ++ suffix
    let reserve := encLinkIterationReserve attempts (state.permutations oracle).base.used
      (state.permutations oracle).overlay.length fuel memory index rest
    run host reserve ⟨labels 7208, memory⟩ =
      (encLinkRowSamples attempts state memory index rest (encLinkInput memory firstKey)).bind fun result =>
        (run host (reserve - result.1.2.1) ⟨labels result.1.2.2, result.1.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.1.2.1)) := by
  dsimp only
  have conditions := encLinkInvariant_conditions attempts state memory index indices suffix firstKey output limit ready
  have wire : memory.bits 0 = encLinkIndexBits index ++ (indices.flatMap encLinkIndexBits ++ suffix) := by
    simpa only [List.flatMap_cons, List.append_assoc] using ready.wire
  rw [encLinkBlock_iteration host attempts _ _ fuel labels present memory index _ wire attemptFits
    conditions.1 conditions.2.1 conditions.2.2.1 conditions.2.2.2]
  rw [← encLinkRowSamples_machine attempts state memory index _ (encLinkInput memory firstKey), PMF.bind_map]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
