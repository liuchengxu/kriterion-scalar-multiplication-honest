import Proof.Privacy.Simulator.Arithmetic.SharedPublicRecovery
import Proof.Privacy.Simulator.Arithmetic.CompiledQueryResponse

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle
open Security.SharedSimulatorMachine GarbledCircuit.SimulatorProtocol
noncomputable section

/-- Each permutation request selects its physical family index. Hash requests use a separate table. -/
def publicSourceOracle : SharedQuery → Fin 15748
  | .fixedForward index _ | .fixedInverse index _ => sharedPhysicalIndex (.inl index)
  | .encForward index _ | .encInverse index _ => sharedPhysicalIndex (.inr index)
  | .hash _ => 0

/-- The request reserve uses the selected finite table count. -/
def publicSourceCount (state : SharedOracleSource) (request : SharedQuery) : Nat :=
  match request with
  | .hash _ => state.family.hash.length
  | _ => (state.family.permutations (publicSourceOracle request)).base.used

/-- Hash requests have no permutation overlay. -/
def publicSourceOverlay (state : SharedOracleSource) (request : SharedQuery) : Nat :=
  match request with
  | .hash _ => 0
  | _ => (state.family.permutations (publicSourceOracle request)).overlay.length

/-- The joint source retains the actual machine result and recovers the full source from its reply. -/
def recordedPublicJoint (attempts : Nat) (memory : Memory) (state : SharedOracleSource)
    (request : SharedQuery) (rest : List Bool) :
    PMF (Option (Configuration 1810 × Nat) × Option (SharedAnswer request × SharedOracleSource)) :=
  (recordedPublicHandlerSamples attempts (publicSourceCount state request)
    (publicSourceOverlay state request) memory request rest).map fun result =>
      (result, result.bind fun final => (answer request (final.1.memory.bits 3)).map fun reply =>
        (reply, sharedPublicNext state request reply))

/-- The first joint marginal retains every exact machine cost and final memory. -/
theorem recordedPublicJoint_machine (attempts : Nat) (memory : Memory) (state : SharedOracleSource)
    (request : SharedQuery) (rest : List Bool) :
    (recordedPublicJoint attempts memory state request rest).map Prod.fst =
      recordedPublicHandlerSamples attempts (publicSourceCount state request)
        (publicSourceOverlay state request) memory request rest := by
  simp only [recordedPublicJoint, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

/-- Exact reply equality suffices because each reply determines its full source update. -/
theorem recordedPublicJoint_source_of_replies (attempts : Nat) (memory : Memory) (state : SharedOracleSource)
    (request : SharedQuery) (rest : List Bool)
    (replies : (recordedPublicHandlerSamples attempts (publicSourceCount state request)
      (publicSourceOverlay state request) memory request rest).map
        (fun result => result.bind fun final => answer request (final.1.memory.bits 3)) =
      (sharedSourceCutoff attempts (.inr request) state).map (Option.map Prod.fst)) :
    (recordedPublicJoint attempts memory state request rest).map Prod.snd =
      sharedSourceCutoff attempts (.inr request) state := by
  have mapped := congrArg (PMF.map (Option.map fun reply => (reply, sharedPublicNext state request reply))) replies
  rw [PMF.map_comp, PMF.map_comp] at mapped
  have left : (recordedPublicJoint attempts memory state request rest).map Prod.snd =
      (recordedPublicHandlerSamples attempts (publicSourceCount state request)
        (publicSourceOverlay state request) memory request rest).map
          ((Option.map fun reply => (reply, sharedPublicNext state request reply)) ∘
            fun result => result.bind fun final => answer request (final.1.memory.bits 3)) := by
    simp only [recordedPublicJoint, PMF.map_comp, Function.comp_def]
    congr 1
    funext result
    cases result <;> rfl
  rw [left, mapped]
  convert sharedPublic_recover attempts state request using 1
  congr 1
  funext result
  cases result <;> rfl

end
end Kriterion.ArgoMAC.ArithmeticSimulator
