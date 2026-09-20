import Proof.Privacy.Simulator.Arithmetic.EncLinkLoopSource
import Proof.Privacy.Simulator.Arithmetic.EncLinkPositions

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SimulatorMachine

/-- The full 508-row machine source has the canonical selected-label program law. -/
theorem encLinkLoopSamples_canonical [BN254.FieldCertificate]
    (attempts : Nat) (firstKey secondKey : Block) (x y : BitVec coordinateBitCount)
    (labels : Fin 508 → Block) (memory : Memory) (state : SparseOracleFamily) (suffix : List Bool)
    (inputBase output limit : Nat)
    (ready : EncLinkLoopMemory state memory encLinkIndices suffix firstKey output limit)
    (stored : EncLinkDataMemory memory 0 inputBase labels x y secondKey)
    (inputLower : 256 ≤ inputBase) (inputUpper : inputBase + 508 ≤ 2 ^ 96)
    (separate : ∀ inputOffset, inputOffset < 508 → ∀ outputOffset, outputOffset < 508 →
      inputBase + inputOffset ≠ output + outputOffset) :
    (encLinkLoopSamples attempts firstKey suffix encLinkIndices memory state).map
      (encLinkLoopValue output 508) =
      (encLinkRowsProgram firstKey secondKey x y labels (List.finRange 508)).cutoffLaw
        (oracleFamilyCutoff attempts) state := by
  have law := encLinkLoopSamples_source attempts firstKey secondKey x y labels (List.finRange 508) 0
    memory state suffix inputBase output limit (by rw [encLinkPositions_indices]; exact ready)
    stored encLinkPositions_consecutive (by simp) inputLower inputUpper (by simpa using separate)
  simpa only [encLinkPositions_indices, List.length_finRange] using law

end Kriterion.ArgoMAC.ArithmeticSimulator
