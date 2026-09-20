import Proof.Privacy.Simulator.Arithmetic.OnlineMachinePreparedRun
import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingWitness
import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The private sampler begins at the fixed scale and point buffer. -/
def onlineSampleInitial (memory : Memory) : Memory := executeLinear onlineSampleSetup memory

/-- Every reached private sample retains the selected output and all later oracle invariants. -/
def OnlineSampledReady [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts limit : Nat) (memory : Memory) (output : BN254.Point)
    (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool) : Prop :=
  ∀ result ∈ (onlineSamplingMemory attempts (onlineSampleInitial memory)).support,
    selectedOutputPoint result.1.ram (BitVec.ofNat 256 onlineInputBase) = some output ∧
    OnlineLinkReady attempts limit
      (onlinePreparedMemory result.1 output (onlineSamplingCoin attempts (onlineSampleInitial memory) result))
      state key suffix

/-- The sampled source runs the selected preparation with the typed coin stored in RAM. -/
noncomputable def onlineSampledSamples [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (memory : Memory) (output : BN254.Point)
    (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool) :
    PMF (Configuration 290305300 × Nat) :=
  (onlineSamplingMemory attempts (onlineSampleInitial memory)).bind fun result =>
    (onlinePreparedSamples attempts result.1 output
      (onlineSamplingCoin attempts (onlineSampleInitial memory) result) state key suffix).map
        fun final => (final.1, final.2 + result.2)

/-- The valid body source includes the sampler's pointer setup. -/
noncomputable def onlineValidBodySamples [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (memory : Memory) (output : BN254.Point)
    (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool) :
    PMF (Configuration 290305300 × Nat) :=
  (onlineSampledSamples attempts memory output state key suffix).map fun result => (result.1, result.2 + 1)

/-- The actual private sampler feeds every supported coin to the complete selected path. -/
theorem onlineMachine_sampled [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts limit : Nat) (memory : Memory) (output : BN254.Point)
    (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool)
    (attemptFits : attempts < 2 ^ 256)
    (ready : OnlineSampledReady attempts limit memory output state key suffix) :
    ClosedRun (onlineMachine attempts) 13622 (onlineSampleInitial memory)
      (onlineSamplingBudget attempts + onlineSelectedReserve attempts limit state)
      (onlineSampledSamples attempts memory output state key suffix) := by
  apply sourceContinuation_close (onlineMachine attempts) 13622 (onlineSampleInitial memory)
    (onlineSamplingBudget attempts) (onlineSelectedReserve attempts limit state)
    (onlineSamplingMemory attempts (onlineSampleInitial memory))
    (fun result => ⟨22393, result.1⟩) Prod.snd
    (fun result => onlinePreparedSamples attempts result.1 output
      (onlineSamplingCoin attempts (onlineSampleInitial memory) result) state key suffix)
  · intro fuel
    exact onlineSamplingBlock_run (onlineMachine attempts) attempts
      (fun pc => onlineBodyLabels 13622 8771 (by decide) 22393 pc.val) (onlineMachine_samples attempts)
      fuel (onlineSampleInitial memory) attemptFits
  · intro result supported
    exact onlineSamplingMemory_cost attempts (onlineSampleInitial memory) result.1 result.2 supported
  · intro result supported
    have words := onlineSamplingCoin_words attempts (onlineSampleInitial memory) result supported
    change WordsAt result.1.ram (BitVec.ofNat 256 onlineSampleBase) 0
      (onlineWords (onlineSamplingCoin attempts (onlineSampleInitial memory) result)) at words
    exact onlineMachine_preparedRun attempts limit result.1 output
      (onlineSamplingCoin attempts (onlineSampleInitial memory) result) state key suffix attemptFits words
      (ready result supported).1 (ready result supported).2

/-- The actual valid body includes every private draw, arithmetic phase, and public oracle phase. -/
theorem onlineMachine_validBody [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts limit : Nat) (memory : Memory) (output : BN254.Point)
    (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool)
    (attemptFits : attempts < 2 ^ 256)
    (ready : OnlineSampledReady attempts limit memory output state key suffix) :
    ClosedRun (onlineMachine attempts) 13621 memory
      (1 + (onlineSamplingBudget attempts + onlineSelectedReserve attempts limit state))
      (onlineValidBodySamples attempts memory output state key suffix) := by
  have setup : FixedContinuation (onlineMachine attempts) 13621 13622 memory (onlineSampleInitial memory) 1 := by
    intro fuel
    exact linear_continue (onlineMachine attempts) onlineSampleSetup
      (onlineBodyLabels 13621 1 (by decide) 13622) (onlineMachine_sampleSetup attempts) memory fuel
  exact setup.close _ _ _ _ _ _ _ _ (onlineMachine_sampled attempts limit memory output state key suffix attemptFits ready)

end Kriterion.ArgoMAC.ArithmeticSimulator
