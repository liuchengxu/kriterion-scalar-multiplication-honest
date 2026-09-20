import Proof.Privacy.Simulator.Arithmetic.EncLinkComplete

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
attribute [local irreducible] encLinkIndices

/-- Each link row preserves the output bit stack. -/
theorem encLinkRowSamples_bits3 (attempts : Nat) (state : SparseOracleFamily)
    (memory : Memory) (index : EncPRF.PermutationIndex) (rest : List Bool) (input : Fin (2 ^ 128))
    (result : EncLinkResult)
    (supported : result ∈ (encLinkRowSamples attempts state memory index rest input).support) :
    result.1.1.bits 3 = memory.bits 3 := by
  obtain ⟨⟨before, spent⟩, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  change (encLinkAfterQuery before).1.bits 3 = _
  rw [encLinkAfterQuery_bits, internalForwardSamples_bits _ _ _ _ before spent member]
  unfold encLinkPrepared
  rw [(encLinkPrepare_state _).2.2.2.2]
  rfl

/-- The complete link loop preserves the output bit stack. -/
theorem encLinkLoopSamples_bits3 (attempts : Nat) (firstKey : Block) (suffix : List Bool)
    (indices : List EncPRF.PermutationIndex) (memory : Memory) (state : SparseOracleFamily)
    (result : EncLinkResult)
    (supported : result ∈ (encLinkLoopSamples attempts firstKey suffix indices memory state).support) :
    result.1.1.bits 3 = memory.bits 3 := by
  induction indices generalizing memory state result with
  | nil =>
      have same := (PMF.mem_support_pure_iff _ _).mp supported
      subst result
      rfl
  | cons index indices ih =>
      obtain ⟨row, member, tail⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      have first := encLinkRowSamples_bits3 attempts state memory index _ _ row member
      split at tail
      · have same := (PMF.mem_support_pure_iff _ _).mp tail
        subst result
        exact first
      · obtain ⟨last, lastMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp tail
        exact (ih row.1.1 row.2 last lastMember).trans first

/-- The complete link source preserves the output bit stack. -/
theorem encLinkSamples_bits3 (attempts : Nat) (memory : Memory) (state : SparseOracleFamily)
    (key : BN254.BaseField) (suffix : List Bool) (result : EncLinkResult)
    (supported : result ∈ (encLinkSamples attempts memory state key suffix).support) :
    result.1.1.bits 3 = memory.bits 3 := by
  obtain ⟨hash, member, tail⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨last, lastMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp tail
  have loop := encLinkLoopSamples_bits3 attempts _ suffix encLinkIndices _ _ last lastMember
  change last.1.1.bits 3 = _
  rw [loop, (encLinkScheduled_memory _).2, Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0)]
  rw [hashHandlerSamples_bits _ _ hash.1 hash.2 member]
  exact congrFun (encLinkSave_state memory).2.2.2.2.2.2.2.2.2 3

end Kriterion.ArgoMAC.ArithmeticSimulator
