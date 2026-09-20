import Proof.Privacy.Simulator.Arithmetic.EncLinkInvariantStep

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The row source operand has the canonical finite block value. -/
noncomputable def encLinkInput (memory : Memory) (firstKey : Block) : Fin (2 ^ 128) :=
  Security.SimulatorMachine.blockFin (xor (encodeBit ((memory.ram 35).getLsbD 0)) firstKey)

/-- The loop invariant links the encoded operand to the actual query register. -/
theorem encLinkInput_operand (state : SparseOracleFamily) (memory : Memory)
    (index : EncPRF.PermutationIndex) (indices : List EncPRF.PermutationIndex) (suffix : List Bool)
    (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit) :
    (encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix)).registers 8 =
      BitVec.ofNat 256 (encLinkInput memory firstKey).val := by
  rw [encLinkInvariant_operand state memory index indices suffix firstKey output limit ready]
  apply BitVec.eq_of_toNat_eq
  simp [encLinkInput, Security.SimulatorMachine.blockFin, BitVec.equivFin]

/-- A nonzero source count gives the machine's next loop entry. -/
theorem encLinkRowQuery_target (attempts : Nat) (state : SparseOracleFamily)
    (memory before : Memory) (spent : Nat) (index : EncPRF.PermutationIndex)
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (supported : (before, spent) ∈ (internalForwardSamples attempts
      (state.permutations (encLinkPhysicalIndex index)).base.used
      (state.permutations (encLinkPhysicalIndex index)).overlay.length
      (encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix))).support)
    (accepted : before.registers 7 ≠ 0#256) :
    (encLinkAfterQuery before).2.2 = if indices = [] then 7466 else 7208 := by
  have room := encLinkInvariant_room state memory index indices suffix firstKey output limit ready
  have fit : 2 * ((state.permutations (encLinkPhysicalIndex index)).base.used + 1) ≤ 2 ^ 110 := by omega
  have kept := encLinkRowQuery_private attempts state memory before spent index _
    ready.represented ready.capacity fit supported
  have cursor : before.ram 33 = BitVec.ofNat 256 output :=
    (kept 33 (by decide) (by decide) (by decide)).trans ready.cursor
  have upper : output < 2 ^ 96 := lt_of_le_of_lt (Nat.le_add_right _ _) ready.outputUpper
  have countSafe : before.ram 33#256 ≠ 38#256 := by
    change before.ram 33 ≠ BitVec.ofNat 256 38
    rw [cursor]
    exact encLinkOutput_separate output 38 ready.outputLower upper (by decide)
  have counter : before.ram 38#256 = BitVec.ofNat 256 (indices.length + 1) := by
    exact (kept 38 (by decide) (by decide) (by decide)).trans ready.counter
  rw [encLinkAfterQuery_target before accepted countSafe, counter, BitVec.ofNat_add]
  simp only [add_sub_cancel_right]
  have lengthFits : indices.length < 2 ^ 256 := by
    have available := ready.room
    simp only [List.length_cons] at available
    norm_num at available ⊢
    omega
  have zero : BitVec.ofNat 256 indices.length = 0#256 ↔ indices = [] := by
    constructor
    · intro equal
      have values := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthFits] at values
      exact List.length_eq_zero_iff.mp values
    · intro empty; simp [empty]
  simp only [zero]

/-- Every accepted source row retains the checked loop invariant. -/
theorem encLinkRowSamples_progress [BN254.FieldCertificate]
    (attempts : Nat) (state : SparseOracleFamily) (memory : Memory)
    (index : EncPRF.PermutationIndex) (indices : List EncPRF.PermutationIndex) (suffix : List Bool)
    (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (result : (Memory × Nat × Fin 7468) × SparseOracleFamily)
    (supported : result ∈ (encLinkRowSamples attempts state memory index
      (indices.flatMap encLinkIndexBits ++ suffix) (encLinkInput memory firstKey)).support) :
    result.1.2.2 = 7467 ∨
      (EncLinkLoopMemory result.2 result.1.1 indices suffix firstKey (output + 1) (limit + 1) ∧
        result.1.2.2 = if indices = [] then 7466 else 7208) := by
  obtain ⟨⟨before, spent⟩, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  change (encLinkAfterQuery before).2.2 = 7467 ∨ _
  by_cases rejected : before.registers 7 = 0#256
  · left; simp [encLinkAfterQuery, rejected]
  · right
    exact ⟨encLinkInvariant_step attempts state memory before spent index indices suffix firstKey output limit ready
      (encLinkInput memory firstKey) (encLinkInput_operand state memory index indices suffix firstKey output limit ready)
      member rejected,
      encLinkRowQuery_target attempts state memory before spent index indices suffix firstKey output limit ready
        member rejected⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
