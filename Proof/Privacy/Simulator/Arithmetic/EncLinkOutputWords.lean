import Proof.Privacy.Simulator.Arithmetic.EncLinkTypedOutput
import Proof.Privacy.Simulator.Arithmetic.EncLinkWideOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SimulatorMachine

/-- Canonical output words represent every typed selected label at full machine width. -/
theorem encLinkOutputMac_wordsAt (memory : Memory) (output : Nat)
    (wide : ∀ offset, offset < 508 → memory.ram (BitVec.ofNat 256 (output + offset)) =
      ((memory.ram (BitVec.ofNat 256 (output + offset))).setWidth 128).setWidth 256) :
    WordsAt memory.ram (BitVec.ofNat 256 output) 0
      ((encLinkMacWords (encLinkOutputMac memory output)).map (fun label => label.setWidth 256)) := by
  rw [encLinkOutputMac_words, encLinkOutput_ofFn]
  intro offset inside
  have valid : offset < 508 := by simpa only [List.length_map, List.length_ofFn] using inside
  simp only [List.getElem_map, List.getElem_ofFn, Nat.zero_add, ← BitVec.ofNat_add]
  exact wide offset valid

/-- The successful full loop retains its complete widened output-array representation. -/
theorem encLinkLoopSamples_wordsAt [BN254.FieldCertificate]
    (attempts : Nat) (firstKey secondKey : Block) (x y : BitVec coordinateBitCount)
    (labels : Fin 508 → Block) (memory : Memory) (state : SparseOracleFamily) (suffix : List Bool)
    (inputBase output limit : Nat)
    (ready : EncLinkLoopMemory state memory encLinkIndices suffix firstKey output limit)
    (stored : EncLinkDataMemory memory 0 inputBase labels x y secondKey)
    (inputLower : 256 ≤ inputBase) (inputUpper : inputBase + 508 ≤ 2 ^ 96)
    (separate : ∀ inputOffset, inputOffset < 508 → ∀ outputOffset, outputOffset < 508 →
      inputBase + inputOffset ≠ output + outputOffset)
    (result : EncLinkResult)
    (supported : result ∈ (encLinkLoopSamples attempts firstKey suffix encLinkIndices memory state).support)
    (accepted : result.1.2.2 ≠ 7467) :
    WordsAt result.1.1.ram (BitVec.ofNat 256 output) 0
      ((encLinkMacWords (encLinkOutputMac result.1.1 output)).map (fun label => label.setWidth 256)) := by
  apply encLinkOutputMac_wordsAt
  have law := encLinkLoopSamples_wide attempts firstKey secondKey x y labels (List.finRange 508) 0
    memory state suffix inputBase output limit (by rw [encLinkPositions_indices]; exact ready)
    stored encLinkPositions_consecutive (by simp) inputLower inputUpper (by simpa using separate) result
    (by rw [encLinkPositions_indices]; exact supported) accepted
  simpa only [List.length_finRange] using law

end Kriterion.ArgoMAC.ArithmeticSimulator
