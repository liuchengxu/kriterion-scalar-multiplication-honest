import Proof.Privacy.Simulator.Arithmetic.EncLinkLoopFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The output observer reads consecutive selected labels from private RAM. -/
def encLinkOutput (memory : Memory) (start : Nat) : Nat → List Block
  | 0 => []
  | count + 1 => (memory.ram (BitVec.ofNat 256 start)).setWidth 128 :: encLinkOutput memory (start + 1) count

/-- The complete observer retains the selected output array and full finite oracle family. -/
def encLinkLoopValue (start count : Nat) (result : EncLinkResult) : Option (List Block × SparseOracleFamily) :=
  if result.1.2.2 = 7467 then none
  else some (encLinkOutput result.1.1 start count, result.2)

/-- A completed row's instruction charge does not change the output observation. -/
theorem encLinkLoopValue_charge (start count cost : Nat) (result : EncLinkResult) :
    encLinkLoopValue start count (encLinkCharge cost result) = encLinkLoopValue start count result := rfl

/-- The remaining loop preserves the previously written first selected label. -/
theorem encLinkLoopValue_cons [BN254.FieldCertificate]
    (attempts : Nat) (firstKey : Block) (suffix : List Bool) (indices : List EncPRF.PermutationIndex)
    (memory : Memory) (state : SparseOracleFamily) (output limit count cost : Nat)
    (ready : EncLinkLoopMemory state memory indices suffix firstKey (output + 1) limit)
    (lower : 256 ≤ output) (result : EncLinkResult)
    (supported : result ∈ (encLinkLoopSamples attempts firstKey suffix indices memory state).support) :
    encLinkLoopValue output (count + 1) (encLinkCharge cost result) =
      (encLinkLoopValue (output + 1) count result).map
        (fun tail => ((memory.ram (BitVec.ofNat 256 output)).setWidth 128 :: tail.1, tail.2)) := by
  have kept := encLinkLoopSamples_beforeOutput attempts firstKey suffix indices memory state (output + 1) limit output
    ready lower (Nat.lt_succ_self output) result supported
  rw [encLinkLoopValue_charge]
  unfold encLinkLoopValue
  split
  · rfl
  · simp only [Option.map_some, encLinkOutput, kept]

/-- The full output map separates the previously written first label from the remaining source. -/
theorem encLinkLoopSamples_outputCons [BN254.FieldCertificate]
    (attempts : Nat) (firstKey : Block) (suffix : List Bool) (indices : List EncPRF.PermutationIndex)
    (memory : Memory) (state : SparseOracleFamily) (output limit count cost : Nat)
    (ready : EncLinkLoopMemory state memory indices suffix firstKey (output + 1) limit)
    (lower : 256 ≤ output) :
    ((encLinkLoopSamples attempts firstKey suffix indices memory state).map (encLinkCharge cost)).map
      (encLinkLoopValue output (count + 1)) =
      ((encLinkLoopSamples attempts firstKey suffix indices memory state).map
        (encLinkLoopValue (output + 1) count)).map (Option.map fun tail =>
          ((memory.ram (BitVec.ofNat 256 output)).setWidth 128 :: tail.1, tail.2)) := by
  rw [PMF.map_comp, PMF.map_comp]
  change PMF.bind _ _ = PMF.bind _ _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  exact congrArg PMF.pure (encLinkLoopValue_cons attempts firstKey suffix indices memory state output limit count cost
    ready lower result supported)

end Kriterion.ArgoMAC.ArithmeticSimulator
