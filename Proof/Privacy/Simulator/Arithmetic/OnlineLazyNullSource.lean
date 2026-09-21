import Proof.Privacy.Simulator.Arithmetic.OnlineLazyRun
import Proof.Privacy.Simulator.Arithmetic.OnlineCurveTyped
import Proof.Privacy.Simulator.Arithmetic.OnlineKeyBuffers
import Proof.Privacy.Simulator.Arithmetic.OnlinePrefixBits
import Proof.Privacy.Simulator.Arithmetic.GateLoopBits

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorSampling Security.SharedSimulatorMachine
noncomputable section
set_option maxRecDepth 4096
attribute [local irreducible] lazyGateLoopResults

/-- The absent-output source programs the exact curve schedule. -/
theorem lazyOnlineNullResult_source [FieldCertificate]
    (memory : Memory) (input : AffineInput) (coin : OfflineCoin)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin)) :
    (lazyOnlineNullResult memory input [] oracle).map (fun result => result.2.1) =
      OperationalOracle.strictCommands oracle
        ((scheduleCommands (((sharedOfflineFrame coin).selectedCurve input).schedule input
          ((sharedOfflineFrame coin).labels input).inputMac)).map sharedCommand) := by
  have source := lazyGateLoopResults_source curveGatePlan
    (curveDirectiveAt ((sharedOfflineFrame coin).selectedCurve input) input
      ((sharedOfflineFrame coin).labels input).inputMac)
    (fun index => coin.1.curve.quotients ⟨index.val / 254, by have := index.isLt; omega⟩
      ⟨index.val % 254, Nat.mod_lt _ (by decide)⟩)
    1270 0 (onlineNullGateInitial (onlineCurveMemory memory input none []))
    (onlineNullGateInitial (onlineCurveMemory memory input none [])) oracle (by decide)
    (GatePrivateAgreement.refl _) (onlineCurveInitial_plan memory input none [] coin stored)
    (onlineCurveInitial_private memory input none [])
  rw [sharedDirectiveLoop_list, curveDirectiveAt_schedule] at source
  simpa only [lazyOnlineNullResult, onlineNullGateInitial, Option.map_map, Function.comp_def] using source

/-- Every successful absent-output run emits the original selected labels. -/
theorem lazyOnlineNullResult_labels [FieldCertificate]
    (memory : Memory) (input : AffineInput) (coin : OfflineCoin)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (empty : memory.bits 3 = [])
    (result : Memory × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex × Nat)
    (success : lazyOnlineNullResult memory input [] oracle = some result) :
    GarbledCircuit.SimulatorProtocol.words 128 508 (result.1.bits 3) =
      some (Lamport.selectedLabels ((sharedOfflineFrame coin).labels input).inputMac) := by
  unfold lazyOnlineNullResult at success
  obtain ⟨raw, reached, equal⟩ := Option.map_eq_some_iff.mp success
  cases equal
  let initial := onlineNullGateInitial (onlineCurveMemory memory input none [])
  have agreement := GatePrivateAgreement.afterLazyLoop curveGatePlan 1270 0 initial initial oracle
    (GatePrivateAgreement.refl initial) raw reached
  have bits := lazyGateLoopResults_bits curveGatePlan 1270 0 initial oracle raw reached
  change GarbledCircuit.SimulatorProtocol.words 128 508
    ((onlineFinalMemory (onlineTagMemory raw.1)).bits 3) = _
  apply onlineFinalMemory_keyProtocol _ coin.2.1 input
  · have keys := onlineCurveMemory_keys memory input none [] coin stored
    intro index inside
    have bound : index < 1016 := by simpa only [inputKeySchedule.wordsLength] using inside
    change raw.1.ram _ = _
    rw [← BitVec.ofNat_add, agreement.words (privateBase + (1 + index))
      (by unfold privateBase; omega) (by unfold privateBase; omega), BitVec.ofNat_add]
    exact keys index inside
  · have coordinates := onlineCurveMemory_coordinates memory input none []
    constructor
    · exact (agreement.words onlineInputBase (by decide) (by decide)).trans coordinates.1
    · have address : BitVec.ofNat 256 onlineInputBase + 1 = BitVec.ofNat 256 (onlineInputBase + 1) := by
        rw [BitVec.ofNat_add]; rfl
      change raw.1.ram _ = _
      rw [address, agreement.words (onlineInputBase + 1) (by decide) (by decide), ← address]
      exact coordinates.2
  · change raw.1.bits 3 = []
    rw [bits]
    rw [onlineNullGateInitial_bits, onlineCurveMemory_bits]
    exact empty

/-- The absent-output parser returns the original labels and strict oracle. -/
theorem lazyOnlineNullResult_parsed [FieldCertificate]
    (memory : Memory) (input : AffineInput) (coin : OfflineCoin)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (empty : memory.bits 3 = []) :
    ((lazyOnlineNullResult memory input [] oracle).bind fun result =>
      (GarbledCircuit.SimulatorProtocol.words 128 508 (result.1.bits 3)).map fun labels => (labels, result.2.1)) =
      (OperationalOracle.strictCommands oracle
        ((scheduleCommands (((sharedOfflineFrame coin).selectedCurve input).schedule input
          ((sharedOfflineFrame coin).labels input).inputMac)).map sharedCommand)).map
        (fun updated => (Lamport.selectedLabels ((sharedOfflineFrame coin).labels input).inputMac, updated)) := by
  rw [← lazyOnlineNullResult_source memory input coin oracle stored, Option.map_map]
  cases reached : lazyOnlineNullResult memory input [] oracle with
  | none => rfl
  | some result =>
    simp only [Option.bind_some, Option.map_some, Function.comp_def]
    rw [lazyOnlineNullResult_labels memory input coin oracle stored empty result reached]
    rfl

end
end Kriterion.ArgoMAC.ArithmeticSimulator
