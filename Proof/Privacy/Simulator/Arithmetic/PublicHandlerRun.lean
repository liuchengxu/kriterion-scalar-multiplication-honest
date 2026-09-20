import Proof.Privacy.Simulator.Arithmetic.PublicHandlerForward
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerInverse
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerHash
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerInput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol

/-- The query family selects one of the three compiled public branches. -/
inductive PublicHandlerKind
  | forward | inverse | hash

/-- The canonical query determines its compiled branch. -/
def publicHandlerKind : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex → PublicHandlerKind
  | .fixedForward _ _ | .encForward _ _ => .forward
  | .fixedInverse _ _ | .encInverse _ _ => .inverse
  | .hash _ => .hash

/-- Each branch begins at its fixed public table label. -/
def publicBranchLabel : PublicHandlerKind → Fin 1772
  | .forward => 102 | .inverse => 299 | .hash => 542

/-- The branch reserve includes every instruction through wire output. -/
def publicBranchReserve (kind : PublicHandlerKind) (attempts count overlayCount : Nat) (memory : Memory) : Nat :=
  match kind with
  | .forward => publicForwardReserve attempts count overlayCount memory
  | .inverse => publicInverseReserve attempts count overlayCount memory
  | .hash => publicHashReserve count memory

/-- The branch conditions state the exact stored counts used by each loop. -/
def PublicBranchCounts (kind : PublicHandlerKind) (attempts count overlayCount : Nat) (memory : Memory) : Prop :=
  match kind with
  | .forward =>
      (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count ∧
      ∀ result ∈ (storedForwardSamples attempts count memory).support,
        result.1.ram (overlayHeader result.1) = BitVec.ofNat 256 overlayCount
  | .inverse =>
      (oracleLoaded memory).ram (overlayHeader (oracleLoaded memory)) = BitVec.ofNat 256 overlayCount ∧
      (inverseLoaded (publicInversePrepared overlayCount memory)).registers 0 = BitVec.ofNat 256 count
  | .hash => (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count

/-- The branch source retains the complete returned memory and its exact instruction charge. -/
noncomputable def publicBranchSamples (kind : PublicHandlerKind) (attempts count overlayCount : Nat)
    (memory : Memory) : PMF (Option (Configuration 1772 × Nat)) :=
  match kind with
  | .forward => (storedForwardSamples attempts count memory).map fun result =>
      some (⟨publicTailLabel result.1, (publicForwardTail overlayCount result.1).1⟩,
        (publicForwardTail overlayCount result.1).2 + (result.2 - 1))
  | .inverse => (storedInverseSamples attempts count (publicInversePrepared overlayCount memory)).map fun result =>
      some (⟨publicTailLabel result.1, (publicInverseTail result.1).1⟩,
        (publicInverseTail result.1).2 + (result.2 - 1) + publicInversePrepareCost overlayCount memory)
  | .hash => (hashHandlerSamples count memory).map fun result =>
      some (⟨publicTailLabel result.1, (publicHashTail result.1).1⟩,
        (publicHashTail result.1).2 + (result.2 - 1))

/-- Every compiled public branch implements its exact memory source. -/
theorem publicHandler_branchRun [BN254.FieldCertificate] (kind : PublicHandlerKind)
    (attempts count overlayCount : Nat) (memory : Memory) (attemptFits : attempts < 2 ^ 256)
    (tableFits : count < 2 ^ 256) (overlayFits : overlayCount < 2 ^ 256)
    (counts : PublicBranchCounts kind attempts count overlayCount memory) :
    run (publicHandler attempts) (publicBranchReserve kind attempts count overlayCount memory)
      ⟨publicBranchLabel kind, memory⟩ = publicBranchSamples kind attempts count overlayCount memory := by
  cases kind with
  | forward => exact publicHandler_forwardRun attempts count overlayCount memory attemptFits tableFits overlayFits counts.1 counts.2
  | inverse => exact publicHandler_inverseRun attempts count overlayCount memory attemptFits tableFits overlayFits counts.1 counts.2
  | hash => exact publicHandler_hashRun attempts count memory tableFits counts

/-- The complete reserve includes canonical input decoding and the selected branch. -/
noncomputable def publicHandlerReserve (attempts count overlayCount : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) : Nat :=
  publicInputCost request + publicBranchReserve (publicHandlerKind request) attempts count overlayCount
    (publicInputMemory memory request rest)

/-- The complete source includes input decoding, oracle state changes, and wire output. -/
noncomputable def publicHandlerSamples (attempts count overlayCount : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) :
    PMF (Option (Configuration 1772 × Nat)) :=
  (publicBranchSamples (publicHandlerKind request) attempts count overlayCount
    (publicInputMemory memory request rest)).map
      (Option.map fun result => (result.1, result.2 + publicInputCost request))

/-- The fixed public machine implements every canonical query through its final wire answer. -/
theorem publicHandler_run [BN254.FieldCertificate] (attempts count overlayCount : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool)
    (wire : memory.bits 0 = query request ++ rest) (attemptFits : attempts < 2 ^ 256)
    (tableFits : count < 2 ^ 256) (overlayFits : overlayCount < 2 ^ 256)
    (counts : PublicBranchCounts (publicHandlerKind request) attempts count overlayCount
      (publicInputMemory memory request rest)) :
    run (publicHandler attempts) (publicHandlerReserve attempts count overlayCount memory request rest) ⟨0, memory⟩ =
      publicHandlerSamples attempts count overlayCount memory request rest := by
  unfold publicHandlerReserve publicHandlerSamples
  rw [publicHandler_input attempts _ memory request rest wire]
  have label : publicInputLabel request = publicBranchLabel (publicHandlerKind request) := by
    cases request <;> rfl
  rw [label, publicHandler_branchRun (publicHandlerKind request) attempts count overlayCount
    (publicInputMemory memory request rest) attemptFits tableFits overlayFits counts]
  rfl

/-- Every branch has one common arithmetic cost bound. -/
theorem publicBranchReserve_bound (kind : PublicHandlerKind) (attempts count overlayCount : Nat)
    (memory : Memory) : publicBranchReserve kind attempts count overlayCount memory ≤
      2574 * attempts + 33 * count + 11 * overlayCount + 2619 := by
  cases kind with
  | forward => have bound := publicForwardReserve_bound attempts count overlayCount memory; exact le_trans bound (by omega)
  | inverse => have bound := publicInverseReserve_bound attempts count overlayCount memory; exact le_trans bound (by omega)
  | hash => have bound := publicHashReserve_bound count memory; exact le_trans bound (by omega)

/-- The complete budget charges the full table and all query instructions. -/
theorem publicHandler_budget (attempts count overlayCount : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) :
    (publicHandler attempts).size + 1 + publicHandlerReserve attempts count overlayCount memory request rest ≤
      2574 * attempts + 33 * count + 11 * overlayCount + 6215 := by
  have inputBound := publicInputCost_bound request
  have branchBound := publicBranchReserve_bound (publicHandlerKind request) attempts count overlayCount
    (publicInputMemory memory request rest)
  change 1771 + 1 + _ ≤ _
  dsimp [publicHandlerReserve]
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
