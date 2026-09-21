import Proof.Privacy.Simulator.Arithmetic.PublicHandlerSourceReplies
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicStable

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security.OperationalOracle

/-- The recorded input reader preserves the selected programmed oracle memory. -/
theorem recordedPublicInputMemory_programmed (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool)
    (oracle : Fin 15749) (state : ProgrammedPermutation (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (fits : 2 * state.base.used ≤ 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110) :
    ProgrammedMemory (recordedPublicInputMemory memory request rest).ram oracle state :=
  ProgrammedMemory.congr memory.ram _ oracle state represented fits overlayFits
    (recordedPublicInputMemory_public memory request rest oracle)

/-- The actual public machine implements both forward query constructors and their operational cutoff law. -/
theorem recordedPublicHandler_forwardSource [BN254.FieldCertificate] (attempts : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool)
    (forward : publicHandlerKind request = .forward)
    (oracle : Fin 15749) (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : (queryOperands request).2.1 = BitVec.ofNat 256 oracle.val)
    (operand : (queryOperands request).1 = BitVec.ofNat 256 input.val)
    (wire : memory.bits 0 = query request ++ rest) (empty : memory.bits 3 = [])
    (attemptFits : attempts < 2 ^ 256)
    (fits : 2 * (state.base.used + 1) ≤ 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110)
    (historyCount : Nat) (history : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount)
    (historyFits : 257 + 2 * historyCount < 2 ^ 110) :
    (run (recordedPublicHandler attempts)
      (recordedPublicHandlerReserve attempts state.base.used state.overlay.length memory request rest) ⟨0, memory⟩).map
      (fun result => result.bind fun result => answer request (result.1.memory.bits 3)) =
      (drawCutoffLaw attempts (state.forward input)).map
        (Option.map fun result => publicAnswerValue request (BitVec.ofNat 256 result.1.val)) := by
  have values := recordedPublicInputMemory_values memory request rest
  have stored := recordedPublicInputMemory_programmed memory request rest oracle state represented (by omega) overlayFits
  have counts : PublicBranchCounts (publicHandlerKind request) attempts state.base.used state.overlay.length
      (recordedPublicInputMemory memory request rest) := by
    rw [forward]
    exact publicHandler_forwardCounts attempts _ oracle state.base state.overlay stored.base stored.overlay
      (values.2.1.trans index) fits
  have tableFits : state.base.used < 2 ^ 256 := lt_of_le_of_lt state.base.within (by decide)
  have overlays : state.overlay.length < 2 ^ 256 := by
    have large : 2 ^ 110 < 2 ^ 256 := by decide
    omega
  have stable := recordedPublic_stable (publicHandlerKind request) attempts state.base.used state.overlay.length historyCount
    (recordedPublicInputMemory memory request rest) oracle (values.2.1.trans index) stored.base.count
    ((recordedPublicInputMemory_public memory request rest oracle 3 0 (by decide)).trans history) fits historyFits
  rw [recordedPublicHandler_answers attempts state.base.used state.overlay.length memory request rest wire empty
    attemptFits tableFits overlays counts stable]
  have source := programmedForwardReplies_typed request attempts (recordedPublicInputMemory memory request rest) oracle
    state input stored (values.2.1.trans index) (values.1.trans operand) (by omega) overlayFits
  cases request with
  | fixedForward index value => simpa only [recordedPublicHandlerReplies] using source
  | encForward index value => simpa only [recordedPublicHandlerReplies] using source
  | fixedInverse _ _ => cases forward
  | encInverse _ _ => cases forward
  | hash _ => cases forward

/-- The actual public machine implements both inverse query constructors and their operational cutoff law. -/
theorem recordedPublicHandler_inverseSource [BN254.FieldCertificate] (attempts : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool)
    (inverse : publicHandlerKind request = .inverse)
    (oracle : Fin 15749) (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : (queryOperands request).2.1 = BitVec.ofNat 256 oracle.val)
    (operand : (queryOperands request).1 = BitVec.ofNat 256 input.val)
    (wire : memory.bits 0 = query request ++ rest) (empty : memory.bits 3 = [])
    (attemptFits : attempts < 2 ^ 256)
    (fits : 2 * (state.base.used + 1) ≤ 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110)
    (historyCount : Nat) (history : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount)
    (historyFits : 257 + 2 * historyCount < 2 ^ 110) :
    (run (recordedPublicHandler attempts)
      (recordedPublicHandlerReserve attempts state.base.used state.overlay.length memory request rest) ⟨0, memory⟩).map
      (fun result => result.bind fun result => answer request (result.1.memory.bits 3)) =
      (drawCutoffLaw attempts (state.inverse input)).map
        (Option.map fun result => publicAnswerValue request (BitVec.ofNat 256 result.1.val)) := by
  have values := recordedPublicInputMemory_values memory request rest
  have stored := recordedPublicInputMemory_programmed memory request rest oracle state represented (by omega) overlayFits
  have counts : PublicBranchCounts (publicHandlerKind request) attempts state.base.used state.overlay.length
      (recordedPublicInputMemory memory request rest) := by
    rw [inverse]
    exact publicHandler_inverseCounts attempts _ oracle state.base state.overlay stored.base stored.overlay
      (values.2.1.trans index)
  have tableFits : state.base.used < 2 ^ 256 := lt_of_le_of_lt state.base.within (by decide)
  have overlays : state.overlay.length < 2 ^ 256 := by
    have large : 2 ^ 110 < 2 ^ 256 := by decide
    omega
  have stable := recordedPublic_stable (publicHandlerKind request) attempts state.base.used state.overlay.length historyCount
    (recordedPublicInputMemory memory request rest) oracle (values.2.1.trans index) stored.base.count
    ((recordedPublicInputMemory_public memory request rest oracle 3 0 (by decide)).trans history) fits historyFits
  rw [recordedPublicHandler_answers attempts state.base.used state.overlay.length memory request rest wire empty
    attemptFits tableFits overlays counts stable]
  have source := programmedInverseReplies_typed request attempts (recordedPublicInputMemory memory request rest) oracle
    state input stored (values.2.1.trans index) (values.1.trans operand) (by omega) overlayFits
  cases request with
  | fixedInverse index value => simpa only [recordedPublicHandlerReplies] using source
  | encInverse index value => simpa only [recordedPublicHandlerReplies] using source
  | fixedForward _ _ => cases inverse
  | encForward _ _ => cases inverse
  | hash _ => cases inverse

/-- The actual public machine implements the exact two-block hash source law without a cutoff. -/
theorem recordedPublicHandler_hashSource [BN254.FieldCertificate] (attempts : Nat) (memory : Memory)
    (key : BN254.BaseField) (rest : List Bool) (pairs : HashTable BN254.BaseField (2 ^ 256))
    (represented : HashMemory memory.ram 15748 (hashWordPairs (fun value => BitVec.ofNat 256 value.val) pairs))
    (wire : memory.bits 0 = query (PublicQuery.hash (FixedIndex := Shared.FixedKeyIndex)
      (EncIndex := EncPRF.PermutationIndex) key) ++ rest)
    (empty : memory.bits 3 = []) (attemptFits : attempts < 2 ^ 256) (fits : 2 * pairs.length ≤ 2 ^ 110) :
    (run (recordedPublicHandler attempts)
      (recordedPublicHandlerReserve attempts pairs.length 0 memory (.hash key) rest) ⟨0, memory⟩).map
      (fun result => result.bind fun result =>
        answer (PublicQuery.hash (FixedIndex := Shared.FixedKeyIndex) (EncIndex := EncPRF.PermutationIndex) key)
          (result.1.memory.bits 3)) =
      (pairs.query (by decide) key).distribution.map
        (fun result => some (Security.SimulatorMachine.hashFin.symm result.1)) := by
  let request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex := .hash key
  have values := recordedPublicInputMemory_values memory request rest
  have stored : HashMemory (recordedPublicInputMemory memory request rest).ram 15748
      (hashWordPairs (fun value => BitVec.ofNat 256 value.val) pairs) := by
    apply HashMemory.congr memory.ram _ 15748 _ represented
    · simpa only [hashWordPairs, List.length_map] using fits
    · exact recordedPublicInputMemory_public memory request rest 15748 0
  have index : (recordedPublicInputMemory memory request rest).registers 9 = BitVec.ofNat 256 (15748 : Fin 15749).val := values.2.1
  have counts : PublicBranchCounts .hash attempts pairs.length 0 (recordedPublicInputMemory memory request rest) := by
    simpa only [hashWordPairs, List.length_map] using
      publicHandler_hashCounts attempts 0 (recordedPublicInputMemory memory request rest) 15748 _ stored index
  have tableFits : pairs.length < 2 ^ 256 := by
    have large : 2 ^ 110 < 2 ^ 256 := by decide
    omega
  rw [recordedPublicHandler_answers attempts pairs.length 0 memory request rest wire empty attemptFits tableFits (by decide) counts trivial]
  exact hashReplies_typed pairs key (recordedPublicInputMemory memory request rest) 15748 stored index values.1 fits

end Kriterion.ArgoMAC.ArithmeticSimulator
