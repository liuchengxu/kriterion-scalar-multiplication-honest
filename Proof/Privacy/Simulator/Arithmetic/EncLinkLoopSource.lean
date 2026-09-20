import Proof.Privacy.Simulator.Arithmetic.EncLinkDataSource
import Proof.Privacy.Simulator.Arithmetic.EncLinkOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SimulatorMachine

/-- The complete stored output array has the exact physical source-program law. -/
theorem encLinkLoopSamples_source [BN254.FieldCertificate]
    (attempts : Nat) (firstKey secondKey : Block) (x y : BitVec coordinateBitCount)
    (labels : Fin 508 → Block) (positions : List (Fin 508)) (position : Nat)
    (memory : Memory) (state : SparseOracleFamily) (suffix : List Bool)
    (inputBase output limit : Nat)
    (ready : EncLinkLoopMemory state memory (positions.map encLinkIndexAt) suffix firstKey output limit)
    (stored : EncLinkDataMemory memory position inputBase labels x y secondKey)
    (ordered : EncLinkConsecutive position positions) (remaining : position + positions.length = 508)
    (inputLower : 256 ≤ inputBase) (inputUpper : inputBase + 508 ≤ 2 ^ 96)
    (separate : ∀ inputOffset, inputOffset < 508 → ∀ outputOffset, outputOffset < positions.length →
      inputBase + inputOffset ≠ output + outputOffset) :
    (encLinkLoopSamples attempts firstKey suffix (positions.map encLinkIndexAt) memory state).map
      (encLinkLoopValue output positions.length) =
      (encLinkRowsProgram firstKey secondKey x y labels positions).cutoffLaw (oracleFamilyCutoff attempts) state := by
  induction positions generalizing position memory state output limit with
  | nil =>
      simp only [List.map_nil, List.length_nil, encLinkLoopSamples, PMF.pure_map,
        encLinkLoopValue, show (7466 : Fin 7468) ≠ 7467 from by decide, if_false,
        encLinkOutput, encLinkRowsProgram, Program.cutoffLaw]
  | cons head positions ih =>
      have headPosition := encLinkConsecutive_head position head positions ordered
      have current : EncLinkDataMemory memory head.val inputBase labels x y secondKey := by
        rw [headPosition]; exact stored
      have rowLaw := encLinkRowSamples_dataSource attempts state memory head (positions.map encLinkIndexAt) suffix
        firstKey output limit inputBase ready labels x y secondKey current
      rw [encLinkRowsProgram_step, ← rowLaw]
      simp only [List.map_cons, encLinkLoopSamples, PMF.map_bind, bindCutoff, PMF.bind_map]
      apply Security.ThreePhase.bind_eq_on_support
      intro row rowMember
      dsimp only [Function.comp_def]
      by_cases failed : row.1.2.2 = 7467
      · simp only [if_pos failed, PMF.pure_map, encLinkLoopValue, encLinkRowValue, failed, if_true]
      · have progress := encLinkRowSamples_progress attempts state memory (encLinkIndexAt head)
          (positions.map encLinkIndexAt) suffix firstKey output limit ready row rowMember
        have next := (progress.resolve_left failed).1
        have nextData := encLinkRowSamples_data attempts state memory (encLinkIndexAt head)
          (positions.map encLinkIndexAt) suffix firstKey output limit ready head inputBase labels x y secondKey current
          (by simp only [List.length_map]; simp only [List.length_cons] at remaining; omega)
          inputLower inputUpper (fun offset inside => by simpa only [Nat.add_zero] using separate offset inside 0 (by simp))
          row rowMember failed
        have data : EncLinkDataMemory row.1.1 (position + 1) inputBase labels x y secondKey := by
          simpa only [headPosition] using nextData
        have nextSeparate : ∀ inputOffset, inputOffset < 508 → ∀ outputOffset, outputOffset < positions.length →
            inputBase + inputOffset ≠ (output + 1) + outputOffset := by
          intro inputOffset inside outputOffset valid
          have distinct := separate inputOffset inside (outputOffset + 1) (by simpa using Nat.add_lt_add_right valid 1)
          simpa only [Nat.add_assoc, Nat.add_comm 1 outputOffset] using distinct
        have tailLaw := ih (position + 1) row.1.1 row.2 (output + 1) (limit + 1) next data
          (encLinkConsecutive_tail position head positions ordered)
          (by simp only [List.length_cons] at remaining; omega) nextSeparate
        simp only [if_neg failed, List.length_cons]
        rw [encLinkLoopSamples_outputCons attempts firstKey suffix (positions.map encLinkIndexAt)
          row.1.1 row.2 output (limit + 1) positions.length row.1.2.1 next ready.outputLower, tailLaw]
        simp only [encLinkRowValue, if_neg failed]

end Kriterion.ArgoMAC.ArithmeticSimulator
