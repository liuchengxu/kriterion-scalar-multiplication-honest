import Proof.Privacy.Simulator.Arithmetic.OnlineMachineGates
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineSetup
import Proof.Privacy.Simulator.Arithmetic.EncLinkCompleteBudget

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The link entry retains the finite oracle family and all reached gate invariants. -/
structure OnlineLinkReady [BN254.FieldCertificate] (attempts limit : Nat) (memory : Memory)
    (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool) : Prop where
  represented : OracleFamilyMemory memory.ram state
  capacity : OracleFamilyFits state
  operand : memory.registers 8 = hashKeyWord key
  outputBase : memory.registers 14 = BitVec.ofNat 256 onlineLinkedBase
  baseCount : ∀ index, (state.permutations index).base.used ≤ limit
  overlayCount : ∀ index, (state.permutations index).overlay.length ≤ limit
  room : 2 * (limit + 508) + 256 < 2 ^ 110
  hashRoom : 2 * (state.hash.length + 1) + 256 < 2 ^ 110
  wire : memory.bits 0 = suffix
  later : ∀ result ∈ (encLinkSamples attempts memory state key suffix).support,
    result.1.2.2 = 7466 → OnlineGateReady attempts limit result.1.1

/-- Every successful link continues with the complete ordered gate source. -/
noncomputable def onlineAfterLinkSamples [BN254.FieldCertificate] (attempts : Nat) (result : EncLinkResult) :
    PMF (Configuration 290305300 × Nat) :=
  if result.1.2.2 = 7466 then onlineGateSamples attempts result.1.1
  else PMF.pure (⟨290305299, result.1.1⟩, 1)

/-- The valid online oracle source runs the link before both gate phases. -/
noncomputable def onlineLinkSamples [BN254.FieldCertificate] (attempts : Nat) (memory : Memory)
    (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool) :
    PMF (Configuration 290305300 × Nat) :=
  (encLinkSamples attempts memory state key suffix).bind fun result =>
    (onlineAfterLinkSamples attempts result).map fun final => (final.1, final.2 + result.1.2.1)

/-- The actual link and both gate phases implement the complete ordered oracle source. -/
theorem onlineMachine_linkRun [BN254.FieldCertificate] (attempts limit : Nat) (memory : Memory)
    (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool)
    (attemptFits : attempts < 2 ^ 256) (ready : OnlineLinkReady attempts limit memory state key suffix) :
    ClosedRun (onlineMachine attempts) 1428193 memory
      (encLinkReserve attempts limit 0 memory state + onlineGateReserve attempts limit)
      (onlineLinkSamples attempts memory state key suffix) := by
  have lower : 256 ≤ onlineLinkedBase := by
    have bounds := onlineBuffer_bounds
    omega
  have upper : onlineLinkedBase + 508 < 2 ^ 96 := onlineBuffer_bounds.2.2.2.2.2.2
  have loopReady : ∀ hash ∈ (hashHandlerSamples state.hash.length (encLinkSaved memory)).support,
      EncLinkLoopMemory (encLinkStarted state key hash.1) (encLinkScheduled hash.1) encLinkIndices suffix
        (Security.SimulatorMachine.hashFin.symm (hash.1.registers 8).toFin).1 onlineLinkedBase limit := by
    intro hash supported
    exact encLinkInitialize_ready memory hash.1 hash.2 state key onlineLinkedBase limit suffix
      ready.represented ready.capacity ready.operand ready.outputBase lower upper ready.baseCount ready.overlayCount
      ready.room ready.hashRoom ready.wire supported
  have bounds := encLinkSamples_bounds attempts limit onlineLinkedBase memory state key suffix attemptFits loopReady
  apply sourceContinuation_close (onlineMachine attempts) 1428193 memory
    (encLinkReserve attempts limit 0 memory state) (onlineGateReserve attempts limit)
    (encLinkSamples attempts memory state key suffix)
    (fun result => ⟨onlineBranchLabels 1428193 7466 (by decide) 1435659 result.1.2.2.val, result.1.1⟩)
    (fun result => result.1.2.1) (onlineAfterLinkSamples attempts)
  · intro fuel
    have law := encLinkBlock_complete (onlineMachine attempts) attempts fuel
      (fun pc => onlineBranchLabels 1428193 7466 (by decide) 1435659 pc.val) (onlineMachine_link attempts)
      memory state key onlineLinkedBase limit suffix ready.represented ready.capacity ready.operand ready.outputBase
      lower upper ready.baseCount ready.overlayCount ready.room ready.hashRoom ready.wire attemptFits
    have amount : encLinkReserve attempts limit fuel memory state =
        encLinkReserve attempts limit 0 memory state + fuel := by unfold encLinkReserve; omega
    simp only [encLinkContinue, amount] at law
    exact law
  · intro result supported
    exact (bounds result supported).1
  · intro result supported
    by_cases accepted : result.1.2.2 = 7466
    · simp only [onlineAfterLinkSamples, if_pos accepted, accepted]
      exact onlineMachine_gates attempts limit result.1.1 attemptFits (ready.later result supported accepted)
    · have failed : result.1.2.2 = 7467 := (bounds result supported).2.resolve_left accepted
      simp only [onlineAfterLinkSamples, if_neg accepted, failed]
      exact onlineMachine_cutoffClosed attempts (onlineGateReserve attempts limit) result.1.1
        (by unfold onlineGateReserve; omega)

end Kriterion.ArgoMAC.ArithmeticSimulator
