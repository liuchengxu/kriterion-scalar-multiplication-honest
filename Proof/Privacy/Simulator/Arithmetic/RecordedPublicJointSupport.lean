import Proof.Privacy.Simulator.Arithmetic.RecordedPublicSampleMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine GarbledCircuit.SimulatorProtocol

/-- A successful joint sample retains the actual handler sample and its exact parsed reply. -/
theorem recordedPublicJoint_support (attempts : Nat) (memory : Memory) (state : SharedOracleSource)
    (request : SharedQuery) (rest : List Bool) (result : Configuration 1810 × Nat)
    (reply : SharedAnswer request) (next : SharedOracleSource)
    (supported : (some result, some (reply, next)) ∈ (recordedPublicJoint attempts memory state request rest).support) :
    some result ∈ (recordedPublicHandlerSamples attempts (publicSourceCount state request)
      (publicSourceOverlay state request) memory request rest).support ∧
      answer request (result.1.memory.bits 3) = some reply ∧ next = sharedPublicNext state request reply := by
  obtain ⟨raw, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have first : raw = some result := congrArg Prod.fst same
  subst raw
  have second : (answer request (result.1.memory.bits 3)).map (fun reply => (reply, sharedPublicNext state request reply)) =
      some (reply, next) := congrArg Prod.snd same
  cases decoded : answer request (result.1.memory.bits 3) with
  | none => simp only [decoded, Option.map_none] at second; contradiction
  | some value =>
      rw [decoded, Option.map_some] at second
      obtain ⟨rfl, equal⟩ := Prod.mk.inj (Option.some.inj second)
      exact ⟨member, rfl, equal.symm⟩

/-- A successful source side cannot come from an absent machine result. -/
theorem recordedPublicJoint_sourceSuccess (attempts : Nat) (memory : Memory) (state : SharedOracleSource)
    (request : SharedQuery) (rest : List Bool) (machine : Option (Configuration 1810 × Nat))
    (reply : SharedAnswer request) (next : SharedOracleSource)
    (supported : (machine, some (reply, next)) ∈ (recordedPublicJoint attempts memory state request rest).support) :
    ∃ result, machine = some result := by
  obtain ⟨raw, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have first : raw = machine := congrArg Prod.fst same
  cases raw with
  | none => have second := congrArg Prod.snd same; simp at second
  | some result => exact ⟨result, first.symm⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
