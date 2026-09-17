import Proof.Privacy.Simulator.SimulatorPrivacy
import Proof.Privacy.Simulator.SimulatorMachineLift
import Proof.Privacy.Simulator.SimulatorTotalSampling

namespace Kriterion.ArgoMAC.Security
open Cryptography OperationalOracle BoundedIntegerSampling
namespace SimulatorMachine.ExternalBits

/-- This transform retains the fair-bit count in the sampled value. -/
def withBits {A : Type} : BitCode A → BitCode (A × Nat)
  | .pure value => .pure (value, 0)
  | .bits width next => .bits width fun block =>
      (withBits (next block)).bind fun result => .pure (result.1, width + result.2)

/-- The transform preserves the value, seed, and fair bits of one execution. -/
theorem withBits_run {A Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (code : BitCode A) (seed : Seed) :
    ((withBits code).run random seed) =
      ((((code.run random seed).1.1, (code.run random seed).2),
        (code.run random seed).1.2), (code.run random seed).2) := by
  induction code generalizing seed with
  | pure => rfl
  | bits width next ih => simp only [withBits, BitCode.run, BitCode.bind_run, ih, Nat.add_zero]

/-- The resource transform preserves positive block widths. -/
theorem withBits_positive {A : Type} (code : BitCode A)
    (positive : SimulatorRejectionCost.PositiveWidths code) :
    SimulatorRejectionCost.PositiveWidths (withBits code) := by
  induction code with
  | pure => trivial
  | bits width next ih =>
      exact ⟨positive.1, fun block => SimulatorRejectionCost.positive_bind _ _
        (ih block (positive.2 block)) (fun _ => trivial)⟩

/-- Erasing the retained bit count preserves the complete probability law. -/
theorem withBits_law {A : Type} (code : BitCode A) :
    (withBits code).law.map Prod.fst = code.law := by
  induction code with
  | pure => simp only [withBits, BitCode.law, PMF.pure_map]
  | bits width next ih =>
      simp only [withBits, BitCode.law, BitCode.bind_law, PMF.map_bind,
        PMF.pure_map]
      change (PMF.uniformOfFintype _).bind
        (fun block => ((withBits (next block)).law).map Prod.fst) = _
      simp only [ih]

private abbrev Tape := List (Sigma (fun width : Nat => Fin (2 ^ width)))

private def tapeSource (width : Nat) : Tape → Fin (2 ^ width) × Tape
  | [] => (⟨0, Nat.two_pow_pos width⟩, [])
  | block :: rest =>
      if same : block.1 = width then (same ▸ block.2, rest)
      else (⟨0, Nat.two_pow_pos width⟩, rest)

/-- A finite supported path supplies a concrete fair-block tape. -/
private theorem support_tape {A : Type} (code : BitCode A) (value : A)
    (reached : value ∈ code.law.support) :
    ∃ tape, (code.run tapeSource tape).1.1 = value := by
  induction code with
  | pure answer =>
      simp only [BitCode.law, PMF.mem_support_pure_iff] at reached
      subst value
      exact ⟨[], rfl⟩
  | bits width next ih =>
      obtain ⟨block, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      obtain ⟨tape, same⟩ := ih block member
      exact ⟨⟨width, block⟩ :: tape, by simpa only [BitCode.run, tapeSource, ↓reduceDIte] using same⟩

/-- Every supported stored bit count obeys a bound that holds on every tape. -/
theorem withBits_bound {A : Type} (code : BitCode A) (limit : Nat)
    (bounded : ∀ (Seed : Type) (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) seed,
      (code.run random seed).2 ≤ limit)
    (result : A × Nat) (reached : result ∈ (withBits code).law.support) : result.2 ≤ limit := by
  obtain ⟨tape, same⟩ := support_tape (withBits code) result reached
  rw [withBits_run] at same
  have bits := congrArg Prod.snd same
  rw [← bits]
  exact bounded Tape tapeSource tape

/-- Every fallback draw has support in the original sparse distribution. -/
theorem totalDraw_supported {A : Type} (attempts : Nat) (draw : Draw A) (value : A)
    (reached : value ∈ (totalDraw attempts draw).law.support) :
    value ∈ draw.distribution.support := by
  cases draw with
  | pure answer => exact reached
  | uniform size positive next =>
      simp only [totalDraw, BitCode.bind_law] at reached
      obtain ⟨index, _, same⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      simp only [BitCode.law, PMF.mem_support_pure_iff] at same
      let : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨index, by simp, same.symm⟩

/-- This total external phase always continues after its finite integer sampler. -/
noncomputable def runTotal {A : Type} (attempts : Nat) :
    {budget : Nat} → OracleProgram Garbling.oracleSpec A budget → SparseState → PMF (A × SparseState)
  | _, .pure distribution, state => distribution.map (fun value => (value, state))
  | _, .sample distribution next, state =>
      distribution.bind (fun value => runTotal attempts (next value) state)
  | _, .query request next, state =>
      (totalDraw attempts (externalDraw request state)).law.bind fun answer =>
        runTotal attempts (next answer.1) answer.2

/-- This total interpreter retains sparse charge and fair bits from one execution. -/
noncomputable def runTotalWithResources {A : Type} (attempts : Nat) :
    {budget : Nat} → OracleProgram Garbling.oracleSpec A budget → SparseState → Nat →
      PMF ((A × SparseState) × Nat × Nat)
  | _, .pure distribution, state, _ => distribution.map (fun value => ((value, state), 0, 0))
  | _, .sample distribution next, state, depth =>
      distribution.bind (fun value => runTotalWithResources attempts (next value) state depth)
  | _, .query request next, state, depth =>
      (withBits (totalDraw attempts (externalDraw request state))).law.bind fun sampled =>
        (runTotalWithResources attempts (next sampled.1.1) sampled.1.2 (depth + 1)).map
          (fun result => (result.1, Cost.combinedCharge depth (.inr request) state + result.2.1,
            sampled.2 + result.2.2))

/-- The joint resource fields do not change the total external law. -/
theorem runTotalWithResources_law {A : Type} {budget : Nat} (attempts : Nat)
    (program : OracleProgram Garbling.oracleSpec A budget) (state : SparseState) (depth : Nat) :
    (runTotalWithResources attempts program state depth).map Prod.fst = runTotal attempts program state := by
  induction program generalizing state depth with
  | pure distribution => simp only [runTotalWithResources, runTotal, PMF.map_comp, Function.comp_def]
  | sample distribution next ih => simp only [runTotalWithResources, runTotal, PMF.map_bind, ih]
  | query request next ih =>
      simp only [runTotalWithResources, runTotal, PMF.map_bind, PMF.map_comp, Function.comp_def]
      rw [← withBits_law (totalDraw attempts (externalDraw request state)), PMF.bind_map]
      apply congrArg (PMF.bind (withBits (totalDraw attempts (externalDraw request state))).law)
      funext sampled
      exact ih sampled.1.1 sampled.1.2 (depth + 1)

/-- Every total external phase has bounded sparse work and fair bits.
Every output retains its sparse-state certificate. -/
theorem runTotalWithResources_bound {A : Type} {budget : Nat} (attempts : Nat)
    (program : OracleProgram Garbling.oracleSpec A budget) (state : SparseState)
    (depth capacity : Nat) (bound : Cost.StateBound state capacity) (depthBound : depth ≤ capacity)
    (result : (A × SparseState) × Nat × Nat)
    (reached : result ∈ (runTotalWithResources attempts program state depth).support) :
    result.2.1 ≤ budget * (10 * (capacity + budget) + 16) ∧
      result.2.2 ≤ budget * (257 * attempts) ∧
      Nonempty (Cost.StateBound result.1.2 (capacity + budget)) := by
  induction program generalizing state depth capacity result with
  | pure distribution =>
      simp only [runTotalWithResources] at reached
      obtain ⟨value, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      rw [← same]
      exact ⟨Nat.zero_le _, Nat.zero_le _, ⟨bound.mono (Nat.le_add_right _ _)⟩⟩
  | sample distribution next ih =>
      simp only [runTotalWithResources] at reached
      obtain ⟨value, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      exact ih value state depth capacity bound depthBound result member
  | @query budget request next ih =>
      simp only [runTotalWithResources] at reached
      obtain ⟨sampled, member, tail⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      have sampledSupport : sampled.1 ∈ (totalDraw attempts (externalDraw request state)).law.support := by
        rw [← withBits_law]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨sampled, member, rfl⟩
      obtain ⟨nextBound⟩ := Cost.external_resources request state capacity bound sampled.1
        (totalDraw_supported attempts (externalDraw request state) sampled.1 sampledSupport)
      have head := withBits_bound (totalDraw attempts (externalDraw request state)) (257 * attempts)
        (fun Seed random seed => totalDraw_bits random attempts _
          (combinedDraw_sizeLe (.inr request) state) seed) sampled member
      have step := Cost.combinedCharge_le depth capacity (.inr request) state bound depthBound
      obtain ⟨output, outputReached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp tail
      obtain ⟨sparse, bits, finalBound⟩ := ih sampled.1.1 sampled.1.2 (depth + 1) (capacity + 1)
        nextBound (Nat.add_le_add_right depthBound 1) output outputReached
      rw [← same]
      refine ⟨?_, ?_, ?_⟩
      · dsimp only
        nlinarith
      · dsimp only
        nlinarith
      · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalBound

/-- The total external phase retains the exact handler's common output mass. -/
theorem runTotal_law {A : Type} {budget : Nat} (attempts : Nat)
    (program : OracleProgram Garbling.oracleSpec A budget) (state : SparseState) :
    TotalLaw attempts budget (runSampled externalHandler program state) (runTotal attempts program state) := by
  induction program generalizing state with
  | pure distribution =>
      exact (TotalLaw.exact attempts (distribution.map (fun value => (value, state)))).weaken (Nat.zero_le _)
  | sample distribution next ih => exact TotalLaw.sample distribution (fun value => ih value state)
  | query request next ih =>
      simpa only [runTotal, runSampled, externalHandler, Nat.add_comm] using
        (totalDraw_law attempts (externalDraw request state)).bind (fun answer => ih answer.1 answer.2)

/-- The total resource interpreter has the same common-mass guarantee. -/
theorem runTotalWithResources_totalLaw {A : Type} {budget : Nat} (attempts : Nat)
    (program : OracleProgram Garbling.oracleSpec A budget) (state : SparseState) (depth : Nat) :
    TotalLaw attempts budget (runSampled externalHandler program state)
      ((runTotalWithResources attempts program state depth).map Prod.fst) := by
  rw [runTotalWithResources_law]
  exact runTotal_law attempts program state

end SimulatorMachine.ExternalBits
end Kriterion.ArgoMAC.Security
