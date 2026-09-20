import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerForward
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerInverse
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerHash
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerInput

import Proof.Privacy.Simulator.Arithmetic.PublicHandlerRun

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol

/-- Each branch begins at its fixed public table label. -/
def recordedPublicBranchLabel : PublicHandlerKind → Fin 1810
  | .forward => 102 | .inverse => 299 | .hash => 542

/-- The branch reserve includes every instruction through wire output. -/
def recordedPublicBranchReserve (kind : PublicHandlerKind) (attempts count overlayCount : Nat) (memory : Memory) : Nat :=
  match kind with
  | .forward => recordedPublicForwardReserve attempts count overlayCount memory
  | .inverse => recordedPublicInverseReserve attempts count overlayCount memory
  | .hash => recordedPublicHashReserve count memory

/-- The branch source retains the complete returned memory and its exact instruction charge. -/
noncomputable def recordedPublicBranchSamples (kind : PublicHandlerKind) (attempts count overlayCount : Nat)
    (memory : Memory) : PMF (Option (Configuration 1810 × Nat)) :=
  match kind with
  | .forward => (storedForwardSamples attempts count memory).map fun result =>
      some (⟨recordedPublicTailLabel result.1, (recordedPublicForwardTail overlayCount result.1).1⟩,
        (recordedPublicForwardTail overlayCount result.1).2 + (result.2 - 1))
  | .inverse => (storedInverseSamples attempts count (publicInversePrepared overlayCount memory)).map fun result =>
      some (⟨recordedPublicTailLabel result.1, (recordedPublicInverseTail result.1).1⟩,
        (recordedPublicInverseTail result.1).2 + (result.2 - 1) + publicInversePrepareCost overlayCount memory)
  | .hash => (hashHandlerSamples count memory).map fun result =>
      some (⟨recordedPublicTailLabel result.1, (recordedPublicHashTail result.1).1⟩,
        (recordedPublicHashTail result.1).2 + (result.2 - 1))

/-- Every compiled public branch implements its exact memory source. -/
theorem recordedPublicHandler_branchRun [BN254.FieldCertificate] (kind : PublicHandlerKind)
    (attempts count overlayCount : Nat) (memory : Memory) (attemptFits : attempts < 2 ^ 256)
    (tableFits : count < 2 ^ 256) (overlayFits : overlayCount < 2 ^ 256)
    (counts : PublicBranchCounts kind attempts count overlayCount memory) :
    run (recordedPublicHandler attempts) (recordedPublicBranchReserve kind attempts count overlayCount memory)
      ⟨recordedPublicBranchLabel kind, memory⟩ = recordedPublicBranchSamples kind attempts count overlayCount memory := by
  cases kind with
  | forward => exact recordedPublicHandler_forwardRun attempts count overlayCount memory attemptFits tableFits overlayFits counts.1 counts.2
  | inverse => exact recordedPublicHandler_inverseRun attempts count overlayCount memory attemptFits tableFits overlayFits counts.1 counts.2
  | hash => exact recordedPublicHandler_hashRun attempts count memory tableFits counts

/-- The complete reserve includes canonical input decoding and the selected branch. -/
noncomputable def recordedPublicHandlerReserve (attempts count overlayCount : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) : Nat :=
  publicInputCost request + 4 + recordedPublicBranchReserve (publicHandlerKind request) attempts count overlayCount
    (recordedPublicInputMemory memory request rest)

/-- The complete source includes input decoding, oracle state changes, and wire output. -/
noncomputable def recordedPublicHandlerSamples (attempts count overlayCount : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) :
    PMF (Option (Configuration 1810 × Nat)) :=
  (recordedPublicBranchSamples (publicHandlerKind request) attempts count overlayCount
    (recordedPublicInputMemory memory request rest)).map
      (Option.map fun result => (result.1, result.2 + (publicInputCost request + 4)))

/-- The fixed public machine implements every canonical query through its final wire answer. -/
theorem recordedPublicHandler_run [BN254.FieldCertificate] (attempts count overlayCount : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool)
    (wire : memory.bits 0 = query request ++ rest) (attemptFits : attempts < 2 ^ 256)
    (tableFits : count < 2 ^ 256) (overlayFits : overlayCount < 2 ^ 256)
    (counts : PublicBranchCounts (publicHandlerKind request) attempts count overlayCount
      (recordedPublicInputMemory memory request rest)) :
    run (recordedPublicHandler attempts) (recordedPublicHandlerReserve attempts count overlayCount memory request rest) ⟨0, memory⟩ =
      recordedPublicHandlerSamples attempts count overlayCount memory request rest := by
  unfold recordedPublicHandlerReserve recordedPublicHandlerSamples
  rw [recordedPublicHandler_input attempts _ memory request rest wire]
  have label : recordedPublicCore (publicInputLabel request) = recordedPublicBranchLabel (publicHandlerKind request) := by
    cases request <;> rfl
  rw [label, recordedPublicHandler_branchRun (publicHandlerKind request) attempts count overlayCount
    (recordedPublicInputMemory memory request rest) attemptFits tableFits overlayFits counts]
  rfl

/-- Every branch has one common arithmetic cost bound. -/
theorem recordedPublicBranchReserve_bound (kind : PublicHandlerKind) (attempts count overlayCount : Nat)
    (memory : Memory) : recordedPublicBranchReserve kind attempts count overlayCount memory ≤
      2574 * attempts + 33 * count + 11 * overlayCount + 2619 := by
  cases kind with
  | forward => have bound := recordedPublicForwardReserve_bound attempts count overlayCount memory; exact le_trans bound (by omega)
  | inverse => have bound := recordedPublicInverseReserve_bound attempts count overlayCount memory; exact le_trans bound (by omega)
  | hash => have bound := recordedPublicHashReserve_bound count memory; exact le_trans bound (by omega)

/-- The complete budget charges the full table and all query instructions. -/
theorem recordedPublicHandler_budget (attempts count overlayCount : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) :
    (recordedPublicHandler attempts).size + 1 + recordedPublicHandlerReserve attempts count overlayCount memory request rest ≤
      2574 * attempts + 33 * count + 11 * overlayCount + 6257 := by
  have inputBound := publicInputCost_bound request
  have branchBound := recordedPublicBranchReserve_bound (publicHandlerKind request) attempts count overlayCount
    (recordedPublicInputMemory memory request rest)
  change 1809 + 1 + _ ≤ _
  dsimp [recordedPublicHandlerReserve]
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
