import Proof.Privacy.Simulator.Arithmetic.LinearProgram
import Proof.Privacy.ThreePhasePrivacy

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A fixed prefix returns its exact memory and charges its executed instructions. -/
def FixedContinuation [BN254.FieldCertificate] (host : Machine)
    (entry exit : Fin (host.size + 1)) (initial final : Memory) (cost : Nat) : Prop :=
  ∀ fuel, run host (cost + fuel) ⟨entry, initial⟩ =
    (run host fuel ⟨exit, final⟩).map (Option.map fun result => (result.1, result.2 + cost))

/-- Adjacent fixed prefixes add their exact instruction charges. -/
theorem FixedContinuation.trans [BN254.FieldCertificate] (host : Machine)
    (entry middle exit : Fin (host.size + 1)) (initial prepared final : Memory)
    (firstCost secondCost : Nat)
    (first : FixedContinuation host entry middle initial prepared firstCost)
    (second : FixedContinuation host middle exit prepared final secondCost) :
    FixedContinuation host entry exit initial final (firstCost + secondCost) := by
  intro fuel
  rw [Nat.add_assoc, first, second]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def]
  congr 1
  funext result
  cases result <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A complete path returns its source distribution within one fixed reserve. -/
def ClosedRun [BN254.FieldCertificate] (host : Machine)
    (entry : Fin (host.size + 1)) (memory : Memory) (reserve : Nat)
    (source : PMF (Configuration (host.size + 1) × Nat)) : Prop :=
  ∀ fuel, run host (reserve + fuel) ⟨entry, memory⟩ = source.map some

/-- A fixed prefix retains the complete continuation source and adds its exact charge. -/
theorem FixedContinuation.close [BN254.FieldCertificate] (host : Machine)
    (entry middle : Fin (host.size + 1)) (initial prepared : Memory) (cost reserve : Nat)
    (source : PMF (Configuration (host.size + 1) × Nat))
    (first : FixedContinuation host entry middle initial prepared cost)
    (last : ClosedRun host middle prepared reserve source) :
    ClosedRun host entry initial (cost + reserve)
      (source.map fun result => (result.1, result.2 + cost)) := by
  intro fuel
  rw [Nat.add_assoc, first, last]
  simp only [PMF.map_comp, Function.comp_def, Option.map_some]

/-- A larger reserve keeps the same complete source and actual charge. -/
theorem ClosedRun.mono [BN254.FieldCertificate] (host : Machine)
    (entry : Fin (host.size + 1)) (memory : Memory) (reserve larger : Nat)
    (source : PMF (Configuration (host.size + 1) × Nat))
    (law : ClosedRun host entry memory reserve source) (enough : reserve ≤ larger) :
    ClosedRun host entry memory larger source := by
  intro fuel
  have amount : larger + fuel = reserve + (larger - reserve + fuel) := by omega
  rw [amount]
  exact law _

/-- A bounded source prefix closes with every supported complete continuation. -/
theorem sourceContinuation_close [BN254.FieldCertificate] {A : Type} (host : Machine)
    (entry : Fin (host.size + 1)) (initial : Memory) (reserve tailReserve : Nat)
    (source : PMF A) (next : A → Configuration (host.size + 1)) (cost : A → Nat)
    (tails : A → PMF (Configuration (host.size + 1) × Nat))
    (first : ∀ fuel, run host (reserve + fuel) ⟨entry, initial⟩ = source.bind fun result =>
      (run host (reserve + fuel - cost result) (next result)).map
        (Option.map fun final => (final.1, final.2 + cost result)))
    (bounded : ∀ result ∈ source.support, cost result ≤ reserve)
    (last : ∀ result ∈ source.support, ClosedRun host (next result).pc (next result).memory tailReserve (tails result)) :
    ClosedRun host entry initial (reserve + tailReserve)
      (source.bind fun result => (tails result).map fun final => (final.1, final.2 + cost result)) := by
  intro fuel
  rw [Nat.add_assoc, first, PMF.map_bind]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  have bound := bounded result supported
  have remaining : reserve + (tailReserve + fuel) - cost result =
      tailReserve + (reserve + fuel - cost result) := by omega
  rw [remaining]
  have continued := last result supported (reserve + fuel - cost result)
  have eta : (⟨(next result).pc, (next result).memory⟩ : Configuration (host.size + 1)) = next result := rfl
  rw [eta] at continued
  rw [continued]
  simp only [PMF.map_comp, Function.comp_def, Option.map_some]

end Kriterion.ArgoMAC.ArithmeticSimulator
