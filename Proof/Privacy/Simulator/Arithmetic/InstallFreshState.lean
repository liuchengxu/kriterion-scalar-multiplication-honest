import Proof.Privacy.Simulator.Arithmetic.InstallFresh

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Two RAM writes prepend one pair and preserve every old pair. -/
theorem RepresentsPairs.prepend (ram : Word → Word) (address left right : Word)
    (pairs : List (Word × Word)) (represented : RepresentsPairs ram (address + 2#256) pairs)
    (fits : 2 * pairs.length + 2 ≤ 2 ^ 256) :
    RepresentsPairs (Function.update (Function.update ram address left) (address + 1#256) right)
      address ((left, right) :: pairs) := by
  let memory : Memory := { ram := ram, registers := fun register =>
    if register = 9 then address else if register = 8 then left else if register = 10 then right else 0 }
  have source := pairStored_represents memory pairs (by simpa [memory] using represented) fits
  simpa [memory, pairStored] using source

/-- Installation preserves both complete sparse tables when their cells are disjoint. -/
theorem installedFresh_represents (memory : Memory) (inputs outputs : List (Word × Word))
    (inputStored : RepresentsPairs memory.ram (memory.registers 1) inputs)
    (outputStored : RepresentsPairs memory.ram (memory.registers 3) outputs)
    (inputFits : 2 * inputs.length + 2 ≤ 2 ^ 256)
    (outputFits : 2 * outputs.length + 2 ≤ 2 ^ 256)
    (disjoint : ∀ first, first < 2 * (inputs.length + 1) →
      ∀ second, second < 2 * (outputs.length + 1) →
      memory.registers 1 - 2#256 + BitVec.ofNat 256 first ≠
        memory.registers 3 - 2#256 + BitVec.ofNat 256 second) :
    RepresentsPairs (installedFresh memory).ram ((installedFresh memory).registers 1)
      ((memory.registers 0, memory.ram 6) :: inputs) ∧
    RepresentsPairs (installedFresh memory).ram ((installedFresh memory).registers 3)
      ((memory.registers 0, memory.ram 7) :: outputs) := by
  let input := memory.registers 1 - 2#256
  let output := memory.registers 3 - 2#256
  let firstRam := Function.update (Function.update memory.ram input (memory.registers 0))
    (input + 1#256) (memory.ram 6)
  have inputOld : RepresentsPairs memory.ram (input + 2#256) inputs := by
    simpa [input] using inputStored
  have inputNew := RepresentsPairs.prepend memory.ram input (memory.registers 0)
    (memory.ram 6) inputs inputOld inputFits
  have outputOld : RepresentsPairs firstRam (output + 2#256) outputs := by
    apply RepresentsPairs.congr outputs memory.ram firstRam (output + 2#256)
      (by simpa [output] using outputStored)
    intro index bound
    have first := disjoint 0 (by omega) (index + 2) (by omega)
    have second := disjoint 1 (by omega) (index + 2) (by omega)
    have differentFirst : output + 2#256 + BitVec.ofNat 256 index ≠ input := by
      simpa [input, output, BitVec.ofNat_add, add_assoc, add_comm, add_left_comm] using Ne.symm first
    have differentSecond : output + 2#256 + BitVec.ofNat 256 index ≠ input + 1#256 := by
      simpa [input, output, BitVec.ofNat_add, add_assoc, add_comm, add_left_comm] using Ne.symm second
    simp [firstRam, differentFirst, differentSecond]
  have outputNew := RepresentsPairs.prepend firstRam output (memory.registers 0)
    (memory.ram 7) outputs outputOld outputFits
  constructor
  · change RepresentsPairs (installedFresh memory).ram input _
    apply RepresentsPairs.congr _ firstRam (installedFresh memory).ram input inputNew
    intro index bound
    have first := disjoint index (by simpa using bound) 0 (by omega)
    have second := disjoint index (by simpa using bound) 1 (by omega)
    have differentFirst : input + BitVec.ofNat 256 index ≠ output := by
      simpa [input, output] using first
    have differentSecond : input + BitVec.ofNat 256 index ≠ output + 1#256 := by
      simpa [input, output] using second
    change Function.update (Function.update firstRam output (memory.registers 0))
      (output + 1#256) (memory.ram 7) (input + BitVec.ofNat 256 index) = _
    simp [differentFirst, differentSecond]
  · exact outputNew

end Kriterion.ArgoMAC.ArithmeticSimulator
