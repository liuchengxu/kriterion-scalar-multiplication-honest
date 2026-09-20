import Proof.Privacy.Simulator.Arithmetic.EncLinkCompleteSource
import Proof.Privacy.Simulator.Arithmetic.EncLinkProgramRows

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SimulatorMachine

/-- The complete machine source has the exact original link program output and full family law. -/
theorem encLinkSamples_source [BN254.FieldCertificate] (attempts : Nat)
    (memory : Memory) (state : SparseOracleFamily) (curve : Security.CurveGateRequest) (input : BN254.AffineInput) (mac : InputMac)
    (inputBase output limit : Nat) (suffix : List Bool)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (operand : memory.registers 8 = hashKeyWord (curve.result input))
    (inputPointer : memory.registers 11 = BitVec.ofNat 256 inputBase)
    (inputX : memory.registers 12 = (BitInput.ofAffine input).xBits.setWidth 256) (inputY : memory.registers 13 = (BitInput.ofAffine input).yBits.setWidth 256)
    (outputBase : memory.registers 14 = BitVec.ofNat 256 output)
    (inputLower : 256 ≤ inputBase) (inputUpper : inputBase + 508 ≤ 2 ^ 96)
    (outputLower : 256 ≤ output) (outputUpper : output + 508 < 2 ^ 96)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 inputBase) 0 (List.ofFn fun index => (encLinkMacLabels mac index).setWidth 256))
    (separate : ∀ inputOffset, inputOffset < 508 → ∀ outputOffset, outputOffset < 508 →
      inputBase + inputOffset ≠ output + outputOffset)
    (baseCount : ∀ index, (state.permutations index).base.used ≤ limit)
    (overlayCount : ∀ index, (state.permutations index).overlay.length ≤ limit)
    (room : 2 * (limit + 508) + 256 < 2 ^ 110)
    (hashRoom : 2 * (state.hash.length + 1) + 256 < 2 ^ 110) (wire : memory.bits 0 = suffix) :
    (encLinkSamples attempts memory state (curve.result input) suffix).map (encLinkLoopValue output 508) =
      ((encLinkProgram curve input mac).cutoffLaw (oracleFamilyCutoff attempts) state).map
        (Option.map fun result => (encLinkMacWords result.1, result.2)) := by
  rw [encLinkProgram_rows]
  exact encLinkSamples_rows attempts memory state (curve.result input) inputBase output limit suffix
    (encLinkMacLabels mac) (BitInput.ofAffine input).xBits (BitInput.ofAffine input).yBits represented capacity
    operand inputPointer inputX inputY outputBase inputLower inputUpper outputLower outputUpper stored separate
    baseCount overlayCount room hashRoom wire

end Kriterion.ArgoMAC.ArithmeticSimulator
