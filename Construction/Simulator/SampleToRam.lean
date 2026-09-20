import Construction.Simulator.BoundedSampler

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The storage program retains the sampler labels. -/
def storageLabels (pc : Fin 25) : Fin 26 := ⟨pc.val, by omega⟩

/-- The program stores the sampled word at the address in register eight.
Register seven retains the sampler's acceptance flag. -/
def sampleToRam (size attempts : Nat) : Machine := ⟨25,
  Vector.ofFn (fun pc : Fin 26 =>
    if inside : pc.val < 24 then
      relocate storageLabels ((boundedSampler size attempts).code[pc.val]'(by change pc.val < 25; omega))
    else if pc.val = 24 then .store 8 0 25 else .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
