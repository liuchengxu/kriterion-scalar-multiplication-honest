import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerRun
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicInputFamily
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerTyped
import Proof.Privacy.Simulator.Arithmetic.PublicHistoryResultMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
noncomputable section

/-- The recorded reader preserves the response stack. -/
theorem recordedPublicInputMemory_output (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) :
    (recordedPublicInputMemory memory request rest).bits 3 = memory.bits 3 :=
  (congrFun (publicDispatchMemory_data _).2.2.2.2 3).trans
    ((congrFun (publicHistorySave_state _).2.1 3).trans (queryInputMemory_output memory request rest))

/-- The forward tail emits its exact typed reply after the history update. -/
theorem recordedPublicForwardTail_answer {FixedIndex EncIndex : Type} (request : PublicQuery FixedIndex EncIndex)
    (notHash : ∀ input, request ≠ .hash input) (count : Nat) (memory : Memory) (empty : memory.bits 3 = [])
    (reply : (publicHistoryResult (overlayForwardScan count memory).1).1.registers 8 =
      (overlayForwardScan count memory).1.registers 8) :
    answer request ((recordedPublicForwardTail count memory).1.bits 3) = publicForwardReplyValue request count memory := by
  unfold recordedPublicForwardTail publicForwardReplyValue
  split
  · exact empty ▸ publicHandler_abortAnswer request
  · have emptyScan : (overlayForwardScan count memory).1.bits 3 = [] :=
      (congrFun (overlayForward_data count memory).2.1 3).trans empty
    have observed := publicBlock_value request notHash (publicHistoryResult (overlayForwardScan count memory).1).1
      ((congrFun (publicHistoryResult_bits _) 3).trans emptyScan)
    rw [reply] at observed
    exact observed

/-- The inverse tail emits its exact typed reply after the history update. -/
theorem recordedPublicInverseTail_answer {FixedIndex EncIndex : Type} (request : PublicQuery FixedIndex EncIndex)
    (notHash : ∀ input, request ≠ .hash input) (memory : Memory) (empty : memory.bits 3 = [])
    (reply : (publicHistoryResult memory).1.registers 8 = memory.registers 8) :
    answer request ((recordedPublicInverseTail memory).1.bits 3) = publicReplyValue request memory := by
  unfold recordedPublicInverseTail publicReplyValue
  split
  · exact empty ▸ publicHandler_abortAnswer request
  · have observed := publicBlock_value request notHash (publicHistoryResult memory).1
      ((congrFun (publicHistoryResult_bits memory) 3).trans empty)
    rw [reply] at observed
    exact observed

/-- The history tail preserves the reply on every supported permutation path. -/
def RecordedPublicReplyStable (kind : PublicHandlerKind) (attempts count overlayCount : Nat) (memory : Memory) : Prop :=
  match kind with
  | .forward => ∀ result ∈ (storedForwardSamples attempts count memory).support,
      (publicHistoryResult (overlayForwardScan overlayCount result.1).1).1.registers 8 =
        (overlayForwardScan overlayCount result.1).1.registers 8
  | .inverse => ∀ result ∈ (storedInverseSamples attempts count (publicInversePrepared overlayCount memory)).support,
      (publicHistoryResult result.1).1.registers 8 = result.1.registers 8
  | .hash => True

/-- The source reply law contains no wire encoding or parser computation. -/
noncomputable def recordedPublicHandlerReplies (attempts count overlayCount : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) : PMF (Option request.Answer) :=
  let initial := recordedPublicInputMemory memory request rest
  match request with
  | .fixedForward index value =>
      (storedForwardSamples attempts count initial).map fun result =>
        publicForwardReplyValue (.fixedForward index value) overlayCount result.1
  | .encForward index value =>
      (storedForwardSamples attempts count initial).map fun result =>
        publicForwardReplyValue (.encForward index value) overlayCount result.1
  | .fixedInverse index value =>
      (storedInverseSamples attempts count (publicInversePrepared overlayCount initial)).map fun result =>
        publicReplyValue (.fixedInverse index value) result.1
  | .encInverse index value =>
      (storedInverseSamples attempts count (publicInversePrepared overlayCount initial)).map fun result =>
        publicReplyValue (.encInverse index value) result.1
  | .hash input => (hashHandlerSamples count initial).map fun result => publicReplyValue (.hash input) result.1

/-- The complete source emits exactly its typed replies under the actual answer parser. -/
theorem recordedPublicHandlerSamples_answers (attempts count overlayCount : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool)
    (empty : memory.bits 3 = [])
    (stable : RecordedPublicReplyStable (publicHandlerKind request) attempts count overlayCount
      (recordedPublicInputMemory memory request rest)) :
    (recordedPublicHandlerSamples attempts count overlayCount memory request rest).map
      (fun result => result.bind fun result => answer request (result.1.memory.bits 3)) =
      recordedPublicHandlerReplies attempts count overlayCount memory request rest := by
  have outputEmpty : (recordedPublicInputMemory memory request rest).bits 3 = [] :=
    (recordedPublicInputMemory_output memory request rest).trans empty
  cases request with
  | fixedForward index value =>
      simp only [recordedPublicHandlerSamples, recordedPublicHandlerReplies, publicHandlerKind, recordedPublicBranchSamples,
        PMF.map_comp, Function.comp_def, Option.map_some, Option.bind_some]
      apply publicReply_map
      intro result supported
      exact recordedPublicForwardTail_answer (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) index value) (by intro input; simp) overlayCount result.1
        ((congrFun (storedForwardSamples_bits attempts count _ result.1 result.2 supported) 3).trans outputEmpty)
        (stable result supported)
  | encForward index value =>
      simp only [recordedPublicHandlerSamples, recordedPublicHandlerReplies, publicHandlerKind, recordedPublicBranchSamples,
        PMF.map_comp, Function.comp_def, Option.map_some, Option.bind_some]
      apply publicReply_map
      intro result supported
      exact recordedPublicForwardTail_answer (PublicQuery.encForward (FixedIndex := Shared.FixedKeyIndex) index value) (by intro input; simp) overlayCount result.1
        ((congrFun (storedForwardSamples_bits attempts count _ result.1 result.2 supported) 3).trans outputEmpty)
        (stable result supported)
  | fixedInverse index value =>
      simp only [recordedPublicHandlerSamples, recordedPublicHandlerReplies, publicHandlerKind, recordedPublicBranchSamples,
        PMF.map_comp, Function.comp_def, Option.map_some, Option.bind_some]
      apply publicReply_map
      intro result supported
      exact recordedPublicInverseTail_answer (PublicQuery.fixedInverse (EncIndex := EncPRF.PermutationIndex) index value) (by intro input; simp) result.1
        ((congrFun (storedInverseSamples_bits attempts count _ result.1 result.2 supported) 3).trans
          ((congrFun (publicInversePrepared_bits overlayCount _) 3).trans outputEmpty))
        (stable result supported)
  | encInverse index value =>
      simp only [recordedPublicHandlerSamples, recordedPublicHandlerReplies, publicHandlerKind, recordedPublicBranchSamples,
        PMF.map_comp, Function.comp_def, Option.map_some, Option.bind_some]
      apply publicReply_map
      intro result supported
      exact recordedPublicInverseTail_answer (PublicQuery.encInverse (FixedIndex := Shared.FixedKeyIndex) index value) (by intro input; simp) result.1
        ((congrFun (storedInverseSamples_bits attempts count _ result.1 result.2 supported) 3).trans
          ((congrFun (publicInversePrepared_bits overlayCount _) 3).trans outputEmpty))
        (stable result supported)
  | hash input =>
      simp only [recordedPublicHandlerSamples, recordedPublicHandlerReplies, publicHandlerKind, recordedPublicBranchSamples,
        PMF.map_comp, Function.comp_def, Option.map_some, Option.bind_some]
      apply publicReply_map
      intro result supported
      exact publicHashTail_answer input result.1
        ((congrFun (hashHandlerSamples_bits count _ result.1 result.2 supported) 3).trans outputEmpty)

/-- The actual public machine returns exactly the typed sparse-source reply law. -/
theorem recordedPublicHandler_answers [BN254.FieldCertificate] (attempts count overlayCount : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool)
    (wire : memory.bits 0 = query request ++ rest) (empty : memory.bits 3 = [])
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256) (overlayFits : overlayCount < 2 ^ 256)
    (counts : PublicBranchCounts (publicHandlerKind request) attempts count overlayCount
      (recordedPublicInputMemory memory request rest))
    (stable : RecordedPublicReplyStable (publicHandlerKind request) attempts count overlayCount
      (recordedPublicInputMemory memory request rest)) :
    (run (recordedPublicHandler attempts) (recordedPublicHandlerReserve attempts count overlayCount memory request rest) ⟨0, memory⟩).map
      (fun result => result.bind fun result => answer request (result.1.memory.bits 3)) =
      recordedPublicHandlerReplies attempts count overlayCount memory request rest := by
  rw [recordedPublicHandler_run attempts count overlayCount memory request rest wire attemptFits tableFits overlayFits counts]
  exact recordedPublicHandlerSamples_answers attempts count overlayCount memory request rest empty stable

end
end Kriterion.ArgoMAC.ArithmeticSimulator
