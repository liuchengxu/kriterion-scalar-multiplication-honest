import Proof.Privacy.Simulator.SimulatorExternalBits

namespace Kriterion.ArgoMAC.Security
open Cryptography OperationalOracle BoundedIntegerSampling
namespace SimulatorMachine.ExternalBits

/-- Each result records the queries that this execution makes. -/
structure Execution (A : Type) where
  value : A
  state : SparseState
  queries : Nat
  work : Nat
  bits : Nat

/-- This projection retains the existing resource interface. -/
def Execution.resources {A : Type} (result : Execution A) : (A × SparseState) × Nat × Nat :=
  ((result.value, result.state), result.work, result.bits)

/-- The interpreter increments its query count only when it executes a query. -/
noncomputable def runActual {A : Type} (attempts : Nat) :
    {budget : Nat} → OracleProgram Garbling.oracleSpec A budget → SparseState → Nat → PMF (Execution A)
  | _, .pure distribution, state, _ => distribution.map (fun value => ⟨value, state, 0, 0, 0⟩)
  | _, .sample distribution next, state, depth =>
      distribution.bind (fun value => runActual attempts (next value) state depth)
  | _, .query request next, state, depth =>
      (withBits (totalDraw attempts (externalDraw request state))).law.bind fun sampled =>
        (runActual attempts (next sampled.1.1) sampled.1.2 (depth + 1)).map fun result =>
          { result with
            queries := result.queries + 1
            work := Cost.combinedCharge depth (.inr request) state + result.work
            bits := sampled.2 + result.bits }

/-- The actual query count does not change the result or the previous resource counters. -/
theorem runActual_resources {A : Type} {budget : Nat} (attempts : Nat)
    (program : OracleProgram Garbling.oracleSpec A budget) (state : SparseState) (depth : Nat) :
    (runActual attempts program state depth).map Execution.resources =
      runTotalWithResources attempts program state depth := by
  induction program generalizing state depth with
  | pure distribution => simp only [runActual, runTotalWithResources, PMF.map_comp, Execution.resources, Function.comp_def]
  | sample distribution next ih => simp only [runActual, runTotalWithResources, PMF.map_bind, ih]
  | query request next ih =>
      simp only [runActual, runTotalWithResources, PMF.map_bind, PMF.map_comp]
      apply congrArg (PMF.bind (withBits (totalDraw attempts (externalDraw request state))).law)
      funext sampled
      rw [← ih sampled.1.1 sampled.1.2 (depth + 1), PMF.map_comp]
      rfl

/-- The actual query count does not change the total external game. -/
theorem runActual_law {A : Type} {budget : Nat} (attempts : Nat)
    (program : OracleProgram Garbling.oracleSpec A budget) (state : SparseState) (depth : Nat) :
    (runActual attempts program state depth).map (fun result => (result.value, result.state)) =
      runTotal attempts program state := by
  rw [← runTotalWithResources_law attempts program state depth, ← runActual_resources]
  rw [PMF.map_comp]
  rfl

/-- Every supported execution obeys the bound for its actual query count. -/
theorem runActual_bound {A : Type} {budget : Nat} (attempts : Nat)
    (program : OracleProgram Garbling.oracleSpec A budget) (state : SparseState)
    (depth capacity : Nat) (bound : Cost.StateBound state capacity) (depthBound : depth ≤ capacity)
    (result : Execution A) (reached : result ∈ (runActual attempts program state depth).support) :
    result.queries ≤ budget ∧
      result.work ≤ result.queries * (10 * (capacity + result.queries) + 16) ∧
      result.bits ≤ result.queries * (257 * attempts) ∧
      Nonempty (Cost.StateBound result.state (capacity + result.queries)) := by
  induction program generalizing state depth capacity result with
  | pure distribution =>
      simp only [runActual] at reached
      obtain ⟨value, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      rw [← same]
      exact ⟨Nat.zero_le _, by simp, by simp, by simpa using Nonempty.intro bound⟩
  | sample distribution next ih =>
      simp only [runActual] at reached
      obtain ⟨value, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      exact ih value state depth capacity bound depthBound result member
  | @query budget request next ih =>
      simp only [runActual] at reached
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
      obtain ⟨queries, sparse, bits, finalBound⟩ := ih sampled.1.1 sampled.1.2 (depth + 1) (capacity + 1)
        nextBound (Nat.add_le_add_right depthBound 1) output outputReached
      rw [← same]
      refine ⟨Nat.add_le_add_right queries 1, ?_, ?_, ?_⟩
      · dsimp only
        nlinarith
      · dsimp only
        nlinarith
      · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalBound


/-- The combined bound uses actual external queries and the fixed private allowance. -/
theorem all_phases_bound {Before Chosen Encoded Result Seed : Type}
    {q0 q1 privateBudget q2 : Nat}
    (attempts : Nat) (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (seed : Seed)
    (first : OracleProgram Garbling.oracleSpec Before q0)
    (second : Before → OracleProgram Garbling.oracleSpec Chosen q1)
    (privateStage : Chosen → Program combinedSpec Encoded privateBudget)
    (last : Chosen → Encoded → OracleProgram Garbling.oracleSpec Result q2)
    (before : Execution Before)
    (beforeReached : before ∈ (runActual attempts first (initial initialMetadata) 0).support)
    (chosen : Execution Chosen)
    (chosenReached : chosen ∈ (runActual attempts (second before.value)
      before.state before.queries).support) :
    let depth := before.queries + chosen.queries
    let encoded := Cost.executeTotalCost random attempts (privateStage chosen.value) chosen.state seed depth
    ∀ decided : Execution Result,
      decided ∈ (runActual attempts (last chosen.value encoded.1.1) encoded.1.2.1
        (depth + privateBudget)).support →
      let total := depth + privateBudget + decided.queries
      before.work + chosen.work + encoded.2.2.1 + decided.work ≤ total * (10 * total + 16) ∧
      before.bits + chosen.bits + encoded.2.2.2 + decided.bits ≤ total * (257 * attempts) ∧
      Nonempty (Cost.StateBound decided.state total) := by
  have empty : Cost.StateBound (initial initialMetadata) 0 :=
    Cost.initialBound initialMetadata 0 (by rfl) (by rfl) (by rfl)
  obtain ⟨_, firstCost, firstBits, firstState⟩ := runActual_bound attempts first
    (initial initialMetadata) 0 0 empty (Nat.le_refl _) before beforeReached
  obtain ⟨priorBound⟩ := firstState
  have priorBound' : Cost.StateBound before.state before.queries := by
    simpa only [Nat.zero_add] using priorBound
  obtain ⟨_, secondCost, secondBits, secondState⟩ := runActual_bound attempts
    (second before.value) before.state before.queries before.queries priorBound'
    (Nat.le_refl _) chosen chosenReached
  obtain ⟨selectedBound⟩ := secondState
  let depth := before.queries + chosen.queries
  let encoded := Cost.executeTotalCost random attempts (privateStage chosen.value) chosen.state seed depth
  obtain ⟨_, privateCost, privateState⟩ := Cost.executeTotalCost_resources random attempts
    (privateStage chosen.value) chosen.state seed depth depth selectedBound (Nat.le_refl _)
  have privateBits := Cost.executeTotalCost_bits random attempts
    (privateStage chosen.value) chosen.state seed depth
  obtain ⟨encodedBound⟩ := privateState
  dsimp only
  intro decided decidedReached
  obtain ⟨_, lastCost, lastBits, lastState⟩ := runActual_bound attempts
    (last chosen.value encoded.1.1) encoded.1.2.1 (depth + privateBudget)
    (depth + privateBudget) encodedBound (Nat.le_refl _) decided decidedReached
  let total := depth + privateBudget + decided.queries
  let unit := 10 * total + 16
  have h0 : before.work ≤ before.queries * unit := firstCost.trans
    (Nat.mul_le_mul_left _ (by dsimp [unit, total, depth]; omega))
  have h1 : chosen.work ≤ chosen.queries * unit := secondCost.trans
    (Nat.mul_le_mul_left _ (by dsimp [unit, total, depth]; omega))
  have hp : encoded.2.2.1 ≤ privateBudget * unit := privateCost.trans
    (Nat.mul_le_mul_left _ (by dsimp [unit, total]; omega))
  change decided.work ≤ decided.queries * unit at lastCost
  refine ⟨?_, ?_, lastState⟩
  · have sum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h0 h1) hp) lastCost
    simpa only [← Nat.add_mul] using sum
  · have sum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add firstBits secondBits) privateBits) lastBits
    simpa only [← Nat.add_mul] using sum

end SimulatorMachine.ExternalBits
end Kriterion.ArgoMAC.Security
