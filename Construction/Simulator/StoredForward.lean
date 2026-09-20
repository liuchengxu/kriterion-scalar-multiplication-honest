import Construction.Simulator.OracleMetadata
import Construction.Simulator.PermutationForward

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The persistent forward handler loads metadata, executes the query, and commits its count. -/
def storedForward (attempts : Nat) : Machine := ⟨178, Vector.ofFn (fun pc =>
  if load : pc.val < 22 then
    (oracleLoad[pc.val]'(by change pc.val < 22; exact load)).emit ⟨pc.val + 1, by omega⟩
  else if forward : 22 ≤ pc.val ∧ pc.val < 175 then
    relocate (fun label : Fin 154 => (⟨label.val + 22, by omega⟩ : Fin 179))
      ((permutationForward attempts).code[pc.val - 22]'(by change pc.val - 22 < 154; omega))
  else if commit : 175 ≤ pc.val ∧ pc.val < 178 then
    (oracleCommit[pc.val - 175]'(by change pc.val - 175 < 3; omega)).emit ⟨pc.val + 1, by omega⟩
  else .halt), by decide⟩

def storedLoadLabels (index : Nat) : Fin 179 := ⟨min index 22, by omega⟩
def storedForwardLabels (pc : Fin 154) : Fin 179 := ⟨pc.val + 22, by omega⟩
def storedCommitLabels (index : Nat) : Fin 179 := ⟨175 + min index 3, by omega⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
