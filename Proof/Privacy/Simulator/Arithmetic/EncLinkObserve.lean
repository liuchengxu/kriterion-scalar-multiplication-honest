import Proof.Privacy.Simulator.Arithmetic.EncLinkSelected
import Proof.Privacy.Simulator.Arithmetic.EncLinkLoop

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle

/-- The row observer retains a selected output label only after sampler acceptance. -/
def encLinkRowValue (output : Nat) (result : EncLinkResult) : Option (Block × SparseOracleFamily) :=
  if result.1.2.2 = 7467 then none
  else some ((result.1.1.ram (BitVec.ofNat 256 output)).setWidth 128, result.2)

/-- The finite block observer reads the same low bits as the machine word observer. -/
theorem encLink_sparseWord_block (word : Word) :
    Security.SimulatorMachine.blockFin.symm (sparseWordValue (2 ^ 128) (by decide) word) = word.setWidth 128 := by
  apply BitVec.eq_of_toNat_eq
  simp [Security.SimulatorMachine.blockFin, BitVec.equivFin, sparseWordValue]

/-- The row tail aborts exactly when its public sampler rejects. -/
theorem encLinkAfterQuery_rejected (memory : Memory) :
    (encLinkAfterQuery memory).2.2 = 7467 ↔ memory.registers 7 = 0#256 := by
  unfold encLinkAfterQuery
  split
  · simp_all
  · simp only [encLinkControlState_target]
    split <;> simp_all

/-- The output observer retains the exact selected label and updated source family. -/
theorem encLinkRow_observe (attempts : Nat) (state : SparseOracleFamily)
    (memory before : Memory) (spent : Nat) (index : EncPRF.PermutationIndex)
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (supported : (before, spent) ∈ (internalForwardSamples attempts
      (state.permutations (encLinkPhysicalIndex index)).base.used
      (state.permutations (encLinkPhysicalIndex index)).overlay.length
      (encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix))).support)
    (secondKey label : Block) (key : memory.ram 40 = secondKey.setWidth 256)
    (selected : memory.ram (memory.ram 32) = label.setWidth 256) :
    encLinkRowValue output
      (chargedResult 121 (encLinkQueryPost (before, spent)),
        state.updatePermutation (encLinkPhysicalIndex index)
          (internalForwardMemoryState (state.permutations (encLinkPhysicalIndex index))
            (encLinkInput memory firstKey) before)) =
      (queryValue before).map (fun word =>
        ((Security.SimulatorMachine.blockFin.symm (sparseWordValue (2 ^ 128) (by decide) word) ^^^ secondKey) ^^^ label,
          state.updatePermutation (encLinkPhysicalIndex index)
            (programmedForwardNext (state.permutations (encLinkPhysicalIndex index))
              (encLinkInput memory firstKey) (sparseWordValue (2 ^ 128) (by decide) word)))) := by
  unfold encLinkRowValue
  change (if (encLinkAfterQuery before).2.2 = 7467 then none else some (_, _)) = _
  by_cases rejected : before.registers 7 = 0#256
  · rw [if_pos (encLinkAfterQuery_rejected before |>.mpr rejected)]
    simp [queryValue, rejected]
  · rw [if_neg (fun failed => rejected ((encLinkAfterQuery_rejected before).mp failed))]
    dsimp only [chargedResult, encLinkQueryPost]
    rw [encLinkRowQuery_output attempts state memory before spent index indices suffix firstKey output limit
      ready supported rejected secondKey label key selected]
    simp only [queryValue, if_neg rejected, Option.map_some, encLink_sparseWord_block,
      internalForwardMemoryState]
    simp [queryValue, rejected, BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le]

end Kriterion.ArgoMAC.ArithmeticSimulator
