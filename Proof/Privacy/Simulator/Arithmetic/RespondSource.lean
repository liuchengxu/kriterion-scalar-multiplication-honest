import Proof.Privacy.Simulator.Arithmetic.RunReserve

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A sufficient shared budget preserves the exact completed request source and its charge. -/
theorem respond_source [BN254.FieldCertificate] (machine : Machine) (request : List Bool) (state : State)
    (fuel : Nat) (source : PMF (Configuration (machine.size + 1) × Nat))
    (enough : state.spent + fuel ≤ budget state.queries)
    (implemented : run machine fuel
      ⟨0, {state.memory with bits := Function.update (Function.update state.memory.bits 0 request) 3 []}⟩ =
        source.map some) :
    respond machine request state = source.map (fun result =>
      some (result.1.memory.bits 3, (⟨result.1.memory, state.spent + result.2, state.queries⟩ : State))) := by
  have complete : none ∉ (run machine fuel
      ⟨0, {state.memory with bits := Function.update (Function.update state.memory.bits 0 request) 3 []}⟩).support := by
    rw [implemented]
    simp [PMF.mem_support_map_iff]
  unfold respond
  rw [if_pos (by omega)]
  rw [run_reserve_of_complete machine fuel (budget state.queries - state.spent) _ (by omega) complete,
    implemented, PMF.map_comp]
  rfl

/-- A completed optional source retains the exact memory and charge under the shared reserve. -/
theorem respond_source_optional [BN254.FieldCertificate] (machine : Machine)
    (request : List Bool) (state : State) (fuel : Nat)
    (source : PMF (Option (Configuration (machine.size + 1) × Nat)))
    (enough : state.spent + fuel ≤ budget state.queries)
    (complete : none ∉ source.support)
    (implemented : run machine fuel
      ⟨0, {state.memory with bits := Function.update (Function.update state.memory.bits 0 request) 3 []}⟩ = source) :
    respond machine request state = source.map (Option.map fun result =>
      (result.1.memory.bits 3, (⟨result.1.memory, state.spent + result.2, state.queries⟩ : State))) := by
  unfold respond
  rw [if_pos (by omega)]
  rw [run_reserve_of_complete machine fuel (budget state.queries - state.spent) _ (by omega)
    (by rw [implemented]; exact complete), implemented]

end Kriterion.ArgoMAC.ArithmeticSimulator
