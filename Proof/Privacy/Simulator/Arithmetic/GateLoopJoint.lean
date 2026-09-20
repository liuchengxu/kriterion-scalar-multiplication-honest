import Proof.Privacy.Simulator.Arithmetic.GateDriverJointPrivate
import Proof.Privacy.Simulator.Arithmetic.GateDriverReturns
import Proof.Privacy.Simulator.Arithmetic.GateLoopSource
import Proof.Privacy.Simulator.Arithmetic.ProgramCutoff

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine
noncomputable section

abbrev GateLoopJointResult := (Bool × Memory × Nat) × SharedOracleSource

/-- The joint loop stops on cutoff and retains the exact instruction charge. -/
def gateLoopCoupled {count : Nat} (plan : Vector GateCode count)
    (commands : Fin count → Fin 3 → SharedCommand) (attempts : Nat) :
    Nat → Nat → Memory → SharedOracleSource → PMF (Option GateLoopJointResult)
  | 0, _, memory, state => PMF.pure (some ((true, memory, 0), state))
  | remaining + 1, index, memory, state =>
      if inside : index < count then
        bindCutoff (gateDriverCoupled attempts plan[index] (commands ⟨index, inside⟩) memory state) fun result =>
          (gateLoopCoupled plan commands attempts remaining (index + 1) result.1.2.1 result.2).map
            (Option.map fun tail => ((tail.1.1, tail.1.2.1, result.1.2.2 + tail.1.2.2), tail.2))
      else PMF.pure none

/-- The loop premise specifies each reached gate's stored active commands. -/
def GateLoopCoupledReady {count : Nat} (plan : Vector GateCode count)
    (commands : Fin count → Fin 3 → SharedCommand) (third : Fin count → Bool) (attempts : Nat) :
    Nat → Nat → Nat → Memory → SharedOracleSource → Prop
  | 0, _, _, _, _ => True
  | remaining + 1, index, limit, memory, state =>
      if inside : index < count then
        SharedSourceMemory (gateDriverPrepared plan[index] memory) state limit ∧
        (∀ slot, slot.val < 2 ∨ (gateDriverPrepared plan[index] memory).ram 20 = 3 →
          GateCommandMemory plan[index] slot (gateDriverPrepared plan[index] memory) (commands ⟨index, inside⟩ slot)) ∧
        (gateDriverPrepared plan[index] memory).ram 20 = (if third ⟨index, inside⟩ then 3 else 2) ∧
        ∀ result, some result ∈ (gateDriverCoupled attempts plan[index] (commands ⟨index, inside⟩) memory state).support →
          GateLoopCoupledReady plan commands third attempts remaining (index + 1) (limit + 3) result.1.2.1 result.2
      else False

/-- The source command list has the same gate order as the loop. -/
def gateLoopCommandList {count : Nat} (commands : Fin count → Fin 3 → SharedCommand) (third : Fin count → Bool) :
    Nat → Nat → List SharedCommand
  | 0, _ => []
  | remaining + 1, index =>
      if inside : index < count then
        sharedGateCommandList (commands ⟨index, inside⟩) (third ⟨index, inside⟩) ++ gateLoopCommandList commands third remaining (index + 1)
      else []

/-- The source list appends two command schedules without changing either law. -/
theorem sharedCommandListCutoff_append (attempts : Nat) (first second : List SharedCommand) (state : SharedOracleSource) :
    sharedCommandListCutoff attempts (first ++ second) state =
      bindCutoff (sharedCommandListCutoff attempts first state) (fun result => sharedCommandListCutoff attempts second result.2) := by
  induction first generalizing state with
  | nil => simp only [List.nil_append, sharedCommandListCutoff, bindCutoff, PMF.pure_bind]
  | cons command rest ih =>
    simp only [List.cons_append, sharedCommandListCutoff, ih, bindCutoff_assoc]

/-- The joint loop has the exact complete shared command-list source marginal. -/
theorem gateLoopCoupled_source [BN254.FieldCertificate] {count : Nat} (plan : Vector GateCode count)
    (commands : Fin count → Fin 3 → SharedCommand) (third : Fin count → Bool)
    (attempts remaining index limit : Nat) (memory : Memory) (state : SharedOracleSource)
    (ready : GateLoopCoupledReady plan commands third attempts remaining index limit memory state)
    (room : 256 + 2 * (limit + 3 * remaining) < 2 ^ 110) :
    (gateLoopCoupled plan commands attempts remaining index memory state).map (Option.map fun result => ((), result.2)) =
      sharedCommandListCutoff attempts (gateLoopCommandList commands third remaining index) state := by
  induction remaining generalizing index limit memory state with
  | zero => simp only [gateLoopCoupled, gateLoopCommandList, sharedCommandListCutoff, PMF.pure_map, Option.map_some]
  | succ remaining ih =>
    by_cases inside : index < count
    · simp only [GateLoopCoupledReady, dif_pos inside] at ready
      simp only [gateLoopCoupled, gateLoopCommandList, dif_pos inside, sharedCommandListCutoff_append]
      have projected := cutoff_map_bind (gateDriverCoupled attempts plan[index] (commands ⟨index, inside⟩) memory state)
        (fun result => (gateLoopCoupled plan commands attempts remaining (index + 1) result.1.2.1 result.2).map
          (Option.map fun tail => ((tail.1.1, tail.1.2.1, result.1.2.2 + tail.1.2.2), tail.2)))
        (fun result => ((), result.2)) (fun result => ((), result.2))
        (fun result => sharedCommandListCutoff attempts (gateLoopCommandList commands third remaining (index + 1)) result.2) (by
          intro result supported
          simpa only [PMF.map_comp, Option.map_map, Function.comp_def] using
            ih (index + 1) (limit + 3) result.1.2.1 result.2 (ready.2.2.2 result supported) (by omega))
      rw [projected]
      congr 1
      exact gateDriverCoupled_source attempts limit plan[index] (commands ⟨index, inside⟩) memory state (third ⟨index, inside⟩)
        ready.1 ready.2.1 ready.2.2.1 (by omega)
    · simp only [GateLoopCoupledReady, dif_neg inside] at ready

/-- The joint loop has the exact compiled loop marginal, including every instruction charge. -/
theorem gateLoopCoupled_machine [BN254.FieldCertificate] {count : Nat} (plan : Vector GateCode count)
    (commands : Fin count → Fin 3 → SharedCommand) (third : Fin count → Bool)
    (attempts remaining index limit : Nat) (memory : Memory) (state : SharedOracleSource)
    (ready : GateLoopCoupledReady plan commands third attempts remaining index limit memory state)
    (room : 256 + 2 * (limit + 3 * remaining) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256) :
    (gateLoopCoupled plan commands attempts remaining index memory state).map (Option.map Prod.fst) =
      (gateLoopSamples plan attempts remaining index memory).map (fun result => if result.1 then some result else none) := by
  induction remaining generalizing index limit memory state with
  | zero => simp only [gateLoopCoupled, gateLoopSamples, PMF.pure_map, Option.map_some, ↓reduceIte]
  | succ remaining ih =>
    by_cases inside : index < count
    · simp only [GateLoopCoupledReady, dif_pos inside] at ready
      simp only [gateLoopCoupled, gateLoopSamples, dif_pos inside]
      let charged (result : Fin 1036 × Memory × Nat) := (gateLoopSamples plan attempts remaining (index + 1) result.2.1).map
        (fun tail => if tail.1 then some (tail.1, tail.2.1, result.2.2 + tail.2.2) else none)
      have projected := cutoff_map_bind (gateDriverCoupled attempts plan[index] (commands ⟨index, inside⟩) memory state)
        (fun result => (gateLoopCoupled plan commands attempts remaining (index + 1) result.1.2.1 result.2).map
          (Option.map fun tail => ((tail.1.1, tail.1.2.1, result.1.2.2 + tail.1.2.2), tail.2)))
        Prod.fst Prod.fst charged (by
          intro result supported
          have mapped := congrArg (PMF.map (Option.map fun tail : Bool × Memory × Nat =>
            (tail.1, tail.2.1, result.1.2.2 + tail.2.2)))
            (ih (index + 1) (limit + 3) result.1.2.1 result.2 (ready.2.2.2 result supported) (by omega))
          simp only [PMF.map_comp, Option.map_map, Function.comp_def] at mapped ⊢
          rw [mapped]
          apply congrArg (fun f => PMF.map f (gateLoopSamples plan attempts remaining (index + 1) result.1.2.1))
          funext tail
          split <;> rfl)
      rw [projected, gateDriverCoupled_machine attempts limit plan[index] (commands ⟨index, inside⟩) memory state
        ready.1 ready.2.1 (by omega) attemptFits]
      simp only [bindCutoff, PMF.bind_map, PMF.map_bind]
      apply Security.ThreePhase.bind_eq_on_support
      intro result supported
      rcases gateDriverSamples_returns attempts plan[index] memory result supported with normal | failed
      · simp only [Function.comp_def, normal, show (1034 : Fin 1036) ≠ 1035 by decide, ↓reduceIte,
          PMF.map_comp]
        rfl
      · simp only [Function.comp_def, failed, show (1035 : Fin 1036) ≠ 1034 by decide, ↓reduceIte,
          PMF.pure_map, Bool.false_eq_true]
    · simp only [GateLoopCoupledReady, dif_neg inside] at ready

end
end Kriterion.ArgoMAC.ArithmeticSimulator
