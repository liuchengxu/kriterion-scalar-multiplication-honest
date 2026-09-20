import Proof.Privacy.Simulator.Arithmetic.EncLinkInitializeMemory
import Proof.Privacy.Simulator.Arithmetic.EncLinkLoopRun
import Proof.Privacy.Simulator.Arithmetic.EncLinkLoopMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The exact hash result supplies the next finite oracle family. -/
def encLinkStarted (state : SparseOracleFamily) (key : BN254.BaseField) (memory : Memory) : SparseOracleFamily :=
  state.updateHash (hashNextTable state.hash key (memory.registers 8).toFin)

/-- Initialization charges the save block, exact hash query, and complete fixed schedule. -/
def encLinkStartCost (result : Memory × Nat) : Nat := 15 + (result.2 - 1 + 7120)

/-- The complete source executes initialization and all 508 fixed loop rows. -/
noncomputable def encLinkSamples (attempts : Nat) (memory : Memory) (state : SparseOracleFamily)
    (key : BN254.BaseField) (suffix : List Bool) : PMF EncLinkResult :=
  (hashHandlerSamples state.hash.length (encLinkSaved memory)).bind fun result =>
    (encLinkLoopSamples attempts (Security.SimulatorMachine.hashFin.symm (result.1.registers 8).toFin).1
      suffix encLinkIndices (encLinkScheduled result.1) (encLinkStarted state key result.1)).map
        (encLinkCharge (encLinkStartCost result))

/-- The complete reserve includes initialization, every fixed loop row, and caller fuel. -/
noncomputable def encLinkReserve (attempts limit fuel : Nat) (memory : Memory) (state : SparseOracleFamily) : Nat :=
  15 + ((hashScan state.hash.length (encLinkSaved memory)).2 + 1844 +
    (7120 + (encLinkLoopBudget attempts limit 508 + fuel)))

/-- The source continuation expands only the fixed initialization record. -/
theorem encLinkInitializeSamples_bind {A : Type} (count : Nat) (memory : Memory)
    (next : (Memory × Nat × Fin 7468) → PMF A) :
    (encLinkInitializeSamples count memory).bind next =
      (hashHandlerSamples count (encLinkSaved memory)).bind fun result =>
        next (encLinkScheduled result.1, encLinkStartCost result, 7208) := by
  simp only [encLinkInitializeSamples, PMF.bind_map, Function.comp_def, chargedResult,
    encLinkInitializePost, encLinkStartCost]

/-- The initialized row source retains its exact preceding instruction charge. -/
theorem encLinkBlock_initialized [BN254.FieldCertificate] (host : Machine) (attempts reserve : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (result : Memory × Nat) (state : SparseOracleFamily) (suffix : List Bool) (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state (encLinkScheduled result.1) encLinkIndices suffix firstKey output limit)
    (attemptFits : attempts < 2 ^ 256)
    (enough : encLinkStartCost result + encLinkLoopBudget attempts limit 508 ≤ reserve) :
    (run host (reserve - encLinkStartCost result) ⟨labels 7208, encLinkScheduled result.1⟩).map
      (Option.map fun final => (final.1, final.2 + encLinkStartCost result)) =
      ((encLinkLoopSamples attempts firstKey suffix encLinkIndices (encLinkScheduled result.1) state).map
        (encLinkCharge (encLinkStartCost result))).bind (encLinkContinue host labels reserve) :=
  encLinkBlock_loopCharged host attempts reserve (encLinkStartCost result) labels present state
    (encLinkScheduled result.1) suffix firstKey output limit ready attemptFits enough

/-- The actual fixed machine implements the entire link in every caller machine. -/
theorem encLinkBlock_complete [BN254.FieldCertificate] (host : Machine) (attempts fuel : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (memory : Memory) (state : SparseOracleFamily) (key : BN254.BaseField)
    (output limit : Nat) (suffix : List Bool)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (operand : memory.registers 8 = hashKeyWord key)
    (outputBase : memory.registers 14 = BitVec.ofNat 256 output)
    (outputLower : 256 ≤ output) (outputUpper : output + 508 < 2 ^ 96)
    (baseCount : ∀ index, (state.permutations index).base.used ≤ limit)
    (overlayCount : ∀ index, (state.permutations index).overlay.length ≤ limit)
    (room : 2 * (limit + 508) + 256 < 2 ^ 110)
    (hashRoom : 2 * (state.hash.length + 1) + 256 < 2 ^ 110)
    (wire : memory.bits 0 = suffix) (attemptFits : attempts < 2 ^ 256) :
    run host (encLinkReserve attempts limit fuel memory state) ⟨labels 0, memory⟩ =
      (encLinkSamples attempts memory state key suffix).bind
        (encLinkContinue host labels (encLinkReserve attempts limit fuel memory state)) := by
  have saved := encLinkSaved_family memory state represented capacity
  have index : (encLinkSaved memory).registers 9 = BitVec.ofNat 256 15748 := (encLinkSave_state memory).2.1
  have counter : (oracleLoaded (encLinkSaved memory)).registers 0 = BitVec.ofNat 256 state.hash.length := by
    rw [oracleLoaded_used _ 15748 index]
    simpa only [hashWordPairs, List.length_map] using saved.hash.count
  have fits : state.hash.length < 2 ^ 256 := by omega
  change run host (15 + ((hashScan state.hash.length (encLinkSaved memory)).2 + 1844 +
    (7120 + (encLinkLoopBudget attempts limit 508 + fuel)))) _ = _
  rw [encLinkBlock_initialize host attempts state.hash.length (encLinkLoopBudget attempts limit 508 + fuel)
    labels present memory fits counter]
  rw [encLinkInitializeSamples_bind, encLinkSamples, PMF.bind_bind]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  have ready := encLinkInitialize_ready memory result.1 result.2 state key output limit suffix
    represented capacity operand outputBase outputLower outputUpper baseCount overlayCount room hashRoom wire supported
  have bound := hashHandlerSamples_cost state.hash.length (encLinkSaved memory) result.1 result.2 supported
  dsimp only [Function.comp_def]
  exact encLinkBlock_initialized host attempts (encLinkReserve attempts limit fuel memory state)
    labels present result (encLinkStarted state key result.1) suffix
    (Security.SimulatorMachine.hashFin.symm (result.1.registers 8).toFin).1 output limit ready attemptFits (by
      dsimp only [encLinkReserve, encLinkStartCost]
      omega)

/-- The complete link reserve has a concrete polynomial instruction bound. -/
theorem encLinkReserve_bound (attempts limit fuel : Nat) (memory : Memory) (state : SparseOracleFamily) :
    (encLink attempts).size + 1 + encLinkReserve attempts limit fuel memory state ≤
      6 * state.hash.length + 16524 + encLinkLoopBudget attempts limit 508 + fuel := by
  have bound := hashHandler_budget state.hash.length (encLinkSaved memory)
  rw [show (encLink attempts).size + 1 = 7468 from rfl]
  unfold encLinkReserve
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
