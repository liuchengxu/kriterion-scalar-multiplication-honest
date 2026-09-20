import Proof.Privacy.Simulator.Arithmetic.AssemblyRun
import Proof.Privacy.ThreePhasePrivacy

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- More fuel leaves a completed machine run and its exact charge unchanged. -/
theorem run_more_of_complete [BN254.FieldCertificate] (machine : Machine) (fuel extra : Nat)
    (state : Configuration (machine.size + 1))
    (complete : none ∉ (run machine fuel state).support) :
    run machine (fuel + extra) state = run machine fuel state := by
  induction fuel generalizing state with
  | zero => exact (complete (by simp [run])).elim
  | succ fuel ih =>
    rw [Nat.succ_add, run, run]
    apply Security.ThreePhase.bind_eq_on_support
    intro outcome supported
    cases outcome with
    | none => rfl
    | some outcome =>
      rcases outcome with ⟨halted, next⟩
      cases halted with
      | true => rfl
      | false =>
        have tailComplete : none ∉ (run machine fuel next).support := by
          intro failed
          apply complete
          rw [run, PMF.mem_support_bind_iff]
          refine ⟨some (false, next), supported, ?_⟩
          exact (PMF.mem_support_map_iff _ _ _).mpr ⟨none, failed, rfl⟩
        dsimp only
        rw [ih next tailComplete]

/-- Any larger reserve implements the same completed run. -/
theorem run_reserve_of_complete [BN254.FieldCertificate] (machine : Machine) (fuel reserve : Nat)
    (state : Configuration (machine.size + 1)) (enough : fuel ≤ reserve)
    (complete : none ∉ (run machine fuel state).support) :
    run machine reserve state = run machine fuel state := by
  rw [show reserve = fuel + (reserve - fuel) by omega]
  exact run_more_of_complete machine fuel (reserve - fuel) state complete

end Kriterion.ArgoMAC.ArithmeticSimulator
