import Proof.Privacy.Simulator.Arithmetic.EncLinkLoopMemory
import Proof.Privacy.Simulator.Arithmetic.EncLinkArrayFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- Every complete row preserves a private word before its current output cursor. -/
theorem encLinkRowSamples_beforeOutput [BN254.FieldCertificate]
    (attempts : Nat) (state : SparseOracleFamily) (memory : Memory)
    (index : EncPRF.PermutationIndex) (indices : List EncPRF.PermutationIndex) (suffix : List Bool)
    (firstKey : Block) (output limit cell : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (lower : 256 ≤ cell) (earlier : cell < output) (result : EncLinkResult)
    (supported : result ∈ (encLinkRowSamples attempts state memory index
      (indices.flatMap encLinkIndexBits ++ suffix) (encLinkInput memory firstKey)).support) :
    result.1.1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  obtain ⟨⟨before, spent⟩, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact encLinkRowQuery_frameNat attempts state memory before spent index indices suffix firstKey output limit
    ready member cell lower (by have := ready.outputUpper; omega) (Nat.ne_of_lt earlier)

/-- The complete loop preserves every output word that it wrote before the current cursor. -/
theorem encLinkLoopSamples_beforeOutput [BN254.FieldCertificate]
    (attempts : Nat) (firstKey : Block) (suffix : List Bool) (indices : List EncPRF.PermutationIndex)
    (memory : Memory) (state : SparseOracleFamily) (output limit cell : Nat)
    (ready : EncLinkLoopMemory state memory indices suffix firstKey output limit)
    (lower : 256 ≤ cell) (earlier : cell < output) (result : EncLinkResult)
    (supported : result ∈ (encLinkLoopSamples attempts firstKey suffix indices memory state).support) :
    result.1.1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  induction indices generalizing memory state output limit result with
  | nil =>
      have equal : result = ((memory, 0, 7466), state) := by simpa [encLinkLoopSamples] using supported
      subst result
      rfl
  | cons index indices ih =>
      obtain ⟨row, rowMember, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      have kept := encLinkRowSamples_beforeOutput attempts state memory index indices suffix firstKey output limit cell
        ready lower earlier row rowMember
      change result ∈ (if row.1.2.2 = 7467 then PMF.pure row else
        (encLinkLoopSamples attempts firstKey suffix indices row.1.1 row.2).map (encLinkCharge row.1.2.1)).support at member
      by_cases failed : row.1.2.2 = 7467
      · rw [if_pos failed] at member
        have equal : result = row := by simpa using member
        subst result
        exact kept
      · rw [if_neg failed] at member
        obtain ⟨tail, tailMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        have progress := encLinkRowSamples_progress attempts state memory index indices suffix firstKey output limit ready row rowMember
        exact (ih row.1.1 row.2 (output + 1) (limit + 1) (progress.resolve_left failed).1
          (by omega) tail tailMember).trans kept

end Kriterion.ArgoMAC.ArithmeticSimulator
