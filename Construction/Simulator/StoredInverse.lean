import Construction.Simulator.StoredForward
import Construction.Simulator.SwapMetadata

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The inverse loader exchanges both sparse tables after the normal metadata load. -/
def inverseLoad : List LinearInstruction := oracleLoad ++ swapMetadata

/-- The inverse commit restores the table order before it writes the count. -/
def inverseCommit : List LinearInstruction := swapMetadata ++ oracleCommit

/-- The inverse source starts with exchanged input and output metadata. -/
def inverseLoaded (memory : Memory) : Memory := metadataSwapped (oracleLoaded memory)

/-- The inverse source commits the count after it restores the original table order. -/
def inverseCommitted (memory : Memory) : Memory := oracleCommitted (metadataSwapped memory)

/-- The persistent inverse handler uses the proved forward machine on exchanged tables. -/
def storedInverse (attempts : Nat) : Machine := ⟨192, Vector.ofFn (fun pc =>
  if load : pc.val < 29 then
    (inverseLoad[pc.val]'(by change pc.val < 29; exact load)).emit ⟨pc.val + 1, by omega⟩
  else if forward : 29 ≤ pc.val ∧ pc.val < 182 then
    relocate (fun label : Fin 154 => (⟨label.val + 29, by omega⟩ : Fin 193))
      ((permutationForward attempts).code[pc.val - 29]'(by change pc.val - 29 < 154; omega))
  else if commit : 182 ≤ pc.val ∧ pc.val < 192 then
    (inverseCommit[pc.val - 182]'(by change pc.val - 182 < 10; omega)).emit ⟨pc.val + 1, by omega⟩
  else .halt), by decide⟩

def storedInverseLoadLabels (index : Nat) : Fin 193 := ⟨min index 29, by omega⟩
def storedInverseForwardLabels (pc : Fin 154) : Fin 193 := ⟨pc.val + 29, by omega⟩
def storedInverseCommitLabels (index : Nat) : Fin 193 := ⟨182 + min index 10, by omega⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
