import Proof.Privacy.Simulator.Arithmetic.EncLinkComplete
import Proof.Privacy.Simulator.Arithmetic.EncLinkCanonicalSource
import Proof.Privacy.Simulator.Arithmetic.EncLinkDataInitialize

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SimulatorMachine Security.OperationalOracle

/-- The stored bridge hash has the exact complete physical family source. -/
theorem encLinkSaved_hashSource (memory : Memory) (state : SparseOracleFamily) (key : BN254.BaseField)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (operand : memory.registers 8 = hashKeyWord key) :
    (hashHandlerSamples state.hash.length (encLinkSaved memory)).map
      (fun result => ((result.1.registers 8).toFin, encLinkStarted state key result.1)) =
      oracleFamilySampled (.inr key) state := by
  have saved := encLinkSave_state memory
  have law := hashHandlerSamples_family_joint (encLinkSaved memory) state key
    (encLinkSaved_family memory state represented capacity) saved.2.1 (saved.1.trans operand) capacity.hash
  simpa only [encLinkStarted, oracleFamilySampled, oracleFamilyDraw, Draw.map_distribution] using law

/-- The complete stored link output has the exact hash and selected-row cutoff source. -/
theorem encLinkSamples_rows [BN254.FieldCertificate] (attempts : Nat)
    (memory : Memory) (state : SparseOracleFamily) (key : BN254.BaseField)
    (inputBase output limit : Nat) (suffix : List Bool) (labels : Fin 508 → Block)
    (x y : BitVec coordinateBitCount)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (operand : memory.registers 8 = hashKeyWord key)
    (inputPointer : memory.registers 11 = BitVec.ofNat 256 inputBase)
    (inputX : memory.registers 12 = x.setWidth 256) (inputY : memory.registers 13 = y.setWidth 256)
    (outputBase : memory.registers 14 = BitVec.ofNat 256 output)
    (inputLower : 256 ≤ inputBase) (inputUpper : inputBase + 508 ≤ 2 ^ 96)
    (outputLower : 256 ≤ output) (outputUpper : output + 508 < 2 ^ 96)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 inputBase) 0 (List.ofFn fun index => (labels index).setWidth 256))
    (separate : ∀ inputOffset, inputOffset < 508 → ∀ outputOffset, outputOffset < 508 →
      inputBase + inputOffset ≠ output + outputOffset)
    (baseCount : ∀ index, (state.permutations index).base.used ≤ limit)
    (overlayCount : ∀ index, (state.permutations index).overlay.length ≤ limit)
    (room : 2 * (limit + 508) + 256 < 2 ^ 110)
    (hashRoom : 2 * (state.hash.length + 1) + 256 < 2 ^ 110) (wire : memory.bits 0 = suffix) :
    (encLinkSamples attempts memory state key suffix).map (encLinkLoopValue output 508) =
      (oracleFamilySampled (.inr key) state).bind fun hash =>
        (encLinkRowsProgram (hashFin.symm hash.1).1 (hashFin.symm hash.1).2 x y labels
          (List.finRange 508)).cutoffLaw (oracleFamilyCutoff attempts) hash.2 := by
  rw [← encLinkSaved_hashSource memory state key represented capacity operand, PMF.bind_map,
    encLinkSamples, PMF.map_bind]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  dsimp only [Function.comp_def]
  have ready := encLinkInitialize_ready memory result.1 result.2 state key output limit suffix
    represented capacity operand outputBase outputLower outputUpper baseCount overlayCount room hashRoom wire supported
  have data := encLinkInitialize_data memory result.1 result.2 state inputBase labels x y represented capacity hashRoom
    inputPointer inputX inputY inputLower inputUpper stored supported
  rw [PMF.map_comp]
  have observe : encLinkLoopValue output 508 ∘ encLinkCharge (encLinkStartCost result) = encLinkLoopValue output 508 := rfl
  rw [observe]
  exact encLinkLoopSamples_canonical attempts _ _ x y labels (encLinkScheduled result.1)
    (encLinkStarted state key result.1) suffix inputBase output limit ready data inputLower inputUpper separate

end Kriterion.ArgoMAC.ArithmeticSimulator
