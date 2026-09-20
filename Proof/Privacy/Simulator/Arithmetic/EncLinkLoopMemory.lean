import Proof.Privacy.Simulator.Arithmetic.EncLinkLoop

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The loop invariant also retains the family on a rejected row. -/
theorem encLinkRowSamples_familyReady [BN254.FieldCertificate]
    (attempts : Nat) (state : SparseOracleFamily) (memory : Memory)
    (index : EncPRF.PermutationIndex) (indices : List EncPRF.PermutationIndex) (suffix : List Bool)
    (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (result : EncLinkResult)
    (supported : result ∈ (encLinkRowSamples attempts state memory index
      (indices.flatMap encLinkIndexBits ++ suffix) (encLinkInput memory firstKey)).support) :
    OracleFamilyMemory result.1.1.ram result.2 ∧ OracleFamilyFits result.2 := by
  have upper : output < 2 ^ 96 := lt_of_le_of_lt (Nat.le_add_right _ _) ready.outputUpper
  apply encLinkRowSamples_family attempts state memory index _ _ ready.represented ready.capacity
    (encLinkInput_operand state memory index indices suffix firstKey output limit ready)
    (encLinkInvariant_room state memory index indices suffix firstKey output limit ready) _ _ _ result supported
  · rw [ready.cursor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans upper (by decide))]
    exact upper
  · change memory.ram 33 ≠ BitVec.ofNat 256 32
    rw [ready.cursor]
    exact encLinkOutput_separate output 32 ready.outputLower upper (by decide)
  · change memory.ram 33 ≠ BitVec.ofNat 256 38
    rw [ready.cursor]
    exact encLinkOutput_separate output 38 ready.outputLower upper (by decide)

/-- Every complete loop result retains the full source family and selects a final return. -/
theorem encLinkLoopSamples_memory [BN254.FieldCertificate]
    (attempts : Nat) (firstKey : Block) (suffix : List Bool) (indices : List EncPRF.PermutationIndex)
    (memory : Memory) (state : SparseOracleFamily) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory indices suffix firstKey output limit)
    (result : EncLinkResult)
    (supported : result ∈ (encLinkLoopSamples attempts firstKey suffix indices memory state).support) :
    OracleFamilyMemory result.1.1.ram result.2 ∧ OracleFamilyFits result.2 ∧
      (result.1.2.2 = 7467 ∨ (result.1.2.2 = 7466 ∧ result.1.1.bits 0 = suffix ∧ result.1.1.ram 38 = 0)) := by
  induction indices generalizing memory state output limit result with
  | nil =>
      have equal : result = ((memory, 0, 7466), state) := by simpa [encLinkLoopSamples] using supported
      subst result
      refine ⟨ready.represented, ready.capacity, Or.inr ⟨rfl, ?_, ?_⟩⟩
      · simpa using ready.wire
      · simpa using ready.counter
  | cons index indices ih =>
      obtain ⟨row, rowMember, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      have progress := encLinkRowSamples_progress attempts state memory index indices suffix firstKey output limit
        ready row rowMember
      change result ∈ (if row.1.2.2 = 7467 then PMF.pure row else
        (encLinkLoopSamples attempts firstKey suffix indices row.1.1 row.2).map (encLinkCharge row.1.2.1)).support at member
      by_cases failed : row.1.2.2 = 7467
      · rw [if_pos failed] at member
        have equal : result = row := by simpa using member
        subst result
        have family := encLinkRowSamples_familyReady attempts state memory index indices suffix firstKey output limit ready row rowMember
        exact ⟨family.1, family.2, Or.inl failed⟩
      · rw [if_neg failed] at member
        obtain ⟨tail, tailMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        exact ih row.1.1 row.2 (output + 1) (limit + 1) (progress.resolve_left failed).1 tail tailMember

end Kriterion.ArgoMAC.ArithmeticSimulator
