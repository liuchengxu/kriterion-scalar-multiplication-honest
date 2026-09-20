import Proof.Privacy.Simulator.Arithmetic.EncLinkReady

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The source result retains the complete machine result and the finite oracle family. -/
abbrev EncLinkResult := (Memory × Nat × Fin 7468) × SparseOracleFamily

/-- The loop adds each completed row's actual charge to the remaining source result. -/
def encLinkCharge (cost : Nat) (result : EncLinkResult) : EncLinkResult :=
  (chargedResult cost result.1, result.2)

/-- The finite loop source stops at the first public sampler cutoff. -/
noncomputable def encLinkLoopSamples (attempts : Nat) (firstKey : Block) (suffix : List Bool) :
    List EncPRF.PermutationIndex → Memory → SparseOracleFamily → PMF EncLinkResult
  | [], memory, state => PMF.pure ((memory, 0, 7466), state)
  | index :: indices, memory, state =>
      (encLinkRowSamples attempts state memory index (indices.flatMap encLinkIndexBits ++ suffix)
        (encLinkInput memory firstKey)).bind fun result =>
          if result.1.2.2 = 7467 then PMF.pure result
          else (encLinkLoopSamples attempts firstKey suffix indices result.1.1 result.2).map
            (encLinkCharge result.1.2.1)

/-- The uniform row allowance bounds arithmetic, scans, and sampler work. -/
def encLinkRowBudget (attempts limit : Nat) : Nat := 2574 * attempts + 44 * limit + 274

/-- The full loop allowance counts each remaining row once. -/
def encLinkLoopBudget (attempts limit count : Nat) : Nat :=
  count * encLinkRowBudget attempts (limit + count)

/-- The growing source cap leaves the common row allowance unchanged. -/
theorem encLinkLoopBudget_step (attempts limit count : Nat) :
    encLinkLoopBudget attempts limit (count + 1) =
      encLinkRowBudget attempts (limit + count + 1) + encLinkLoopBudget attempts (limit + 1) count := by
  unfold encLinkLoopBudget
  rw [show limit + (count + 1) = limit + count + 1 by omega,
    show limit + 1 + count = limit + count + 1 by omega, Nat.add_mul]
  omega

/-- The row source fits the common allowance for every remaining iteration. -/
theorem encLinkRowSamples_budget [BN254.FieldCertificate]
    (attempts : Nat) (state : SparseOracleFamily) (memory : Memory)
    (index : EncPRF.PermutationIndex) (indices : List EncPRF.PermutationIndex) (suffix : List Bool)
    (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (attemptFits : attempts < 2 ^ 256) (result : EncLinkResult)
    (supported : result ∈ (encLinkRowSamples attempts state memory index
      (indices.flatMap encLinkIndexBits ++ suffix) (encLinkInput memory firstKey)).support) :
    result.1.2.1 ≤ encLinkRowBudget attempts (limit + indices.length + 1) := by
  have conditions := encLinkInvariant_conditions attempts state memory index indices suffix firstKey output limit ready
  have member : result.1 ∈ (encLinkIterationSamples attempts
      (state.permutations (encLinkPhysicalIndex index)).base.used
      (state.permutations (encLinkPhysicalIndex index)).overlay.length
      memory index (indices.flatMap encLinkIndexBits ++ suffix)).support := by
    rw [← encLinkRowSamples_machine attempts state memory index _ (encLinkInput memory firstKey)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, supported, rfl⟩
  have used := encLinkIterationSamples_cost attempts _ _ memory index _ result.1
    attemptFits conditions.1 conditions.2.2.1 member
  have bound := encLinkIterationReserve_bound attempts
    (state.permutations (encLinkPhysicalIndex index)).base.used
    (state.permutations (encLinkPhysicalIndex index)).overlay.length 0 memory index
    (indices.flatMap encLinkIndexBits ++ suffix)
  have base := ready.baseCount (encLinkPhysicalIndex index)
  have overlay := ready.overlayCount (encLinkPhysicalIndex index)
  unfold encLinkRowBudget
  omega

/-- Every supported complete loop result stays within the concrete polynomial budget. -/
theorem encLinkLoopSamples_budget [BN254.FieldCertificate]
    (attempts : Nat) (firstKey : Block) (suffix : List Bool) (indices : List EncPRF.PermutationIndex)
    (memory : Memory) (state : SparseOracleFamily) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory indices suffix firstKey output limit)
    (attemptFits : attempts < 2 ^ 256) (result : EncLinkResult)
    (supported : result ∈ (encLinkLoopSamples attempts firstKey suffix indices memory state).support) :
    result.1.2.1 ≤ encLinkLoopBudget attempts limit indices.length := by
  induction indices generalizing memory state output limit result with
  | nil =>
      have equal : result = ((memory, 0, 7466), state) := by simpa [encLinkLoopSamples] using supported
      subst result
      simp [encLinkLoopBudget]
  | cons index indices ih =>
      obtain ⟨row, rowMember, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      have rowBound := encLinkRowSamples_budget attempts state memory index indices suffix firstKey output limit
        ready attemptFits row rowMember
      have progress := encLinkRowSamples_progress attempts state memory index indices suffix firstKey output limit
        ready row rowMember
      change result ∈ (if row.1.2.2 = 7467 then PMF.pure row else
        (encLinkLoopSamples attempts firstKey suffix indices row.1.1 row.2).map (encLinkCharge row.1.2.1)).support at member
      by_cases failed : row.1.2.2 = 7467
      · rw [if_pos failed] at member
        have equal : result = row := by simpa using member
        subst result
        simp only [List.length_cons, encLinkLoopBudget_step]
        omega
      · rw [if_neg failed] at member
        obtain ⟨tail, tailMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        have next := (progress.resolve_left failed).1
        have tailBound := ih row.1.1 row.2 (output + 1) (limit + 1) next tail tailMember
        change row.1.2.1 + tail.1.2.1 ≤ _
        simp only [List.length_cons, encLinkLoopBudget_step]
        omega

end Kriterion.ArgoMAC.ArithmeticSimulator
