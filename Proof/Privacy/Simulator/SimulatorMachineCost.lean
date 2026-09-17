import Proof.Privacy.Simulator.SimulatorRuntime
import Proof.Privacy.Simulator.SimulatorMachineLaw

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography OperationalOracle
namespace SimulatorMachine
namespace Cost

/-- The bound records the only random range that one draw can request. -/
def drawBound {A : Type} : Draw A → Nat
  | .pure _ => 0
  | .uniform size _ _ => size

theorem drawBound_map {A B : Type} (draw : Draw A) (f : A → B) :
    drawBound (draw.map f) = drawBound draw := by
  cases draw <;> rfl

theorem forwardDraw_bound {size : Nat} (state : SparsePermutation size) (input : Fin size) :
    drawBound (state.forward input) ≤ size := by
  unfold SparsePermutation.forward
  dsimp only
  split <;> simp only [drawBound]
  · exact Nat.zero_le _
  · exact Nat.sub_le _ _

theorem inverseDraw_bound {size : Nat} (state : SparsePermutation size) (output : Fin size) :
    drawBound (state.inverse output) ≤ size := by
  unfold SparsePermutation.inverse
  dsimp only
  split <;> simp only [drawBound]
  · exact Nat.zero_le _
  · exact Nat.sub_le _ _

theorem familyDraw_bound {Index : Type} [DecidableEq Index] {size : Nat}
    (request : Index × ProgramAction size) (state : Index → ProgrammedPermutation size) :
    drawBound (familyDraw request state) ≤ size := by
  rcases request with ⟨index, action⟩
  cases action <;> simp only [familyDraw, ProgrammedPermutation.forward,
    ProgrammedPermutation.inverse, ProgrammedPermutation.program, drawBound_map]
  · exact forwardDraw_bound _ _
  · exact inverseDraw_bound _ _
  · exact forwardDraw_bound _ _

theorem hashDraw_bound {Key : Type} [DecidableEq Key] {size : Nat}
    (positive : 0 < size) (table : HashTable Key size) (key : Key) :
    drawBound (table.query positive key) ≤ size := by
  unfold HashTable.query
  split <;> simp only [drawBound]
  · exact Nat.zero_le _
  · exact Nat.le_refl _

theorem lowerDraw_bound (query : lowerSpec.Query) (oracles : OracleData) :
    drawBound (lowerDraw query oracles) ≤ 2 ^ 256 := by
  cases query with
  | inl request =>
      rw [lowerDraw, drawBound_map]
      exact (familyDraw_bound request oracles.1).trans
        (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by decide : 128 ≤ 256))
  | inr key =>
      rw [lowerDraw, drawBound_map]
      exact hashDraw_bound _ _ _

theorem sparseDraw_bound (query : spec.Query) (state : SparseState) :
    drawBound (sparseDraw query state) ≤ 2 ^ 256 := by
  cases query with
  | read request =>
      rw [sparseDraw, drawBound_map]
      exact lowerDraw_bound _ _
  | program command =>
      simp only [sparseDraw]
      split
      · rw [drawBound_map]
        exact lowerDraw_bound _ _
      · exact Nat.zero_le _

/-- Every internal or external request samples at most a 256-bit integer range. -/
theorem combinedDraw_bound (query : combinedSpec.Query) (state : SparseState) :
    drawBound (combinedDraw query state) ≤ 2 ^ 256 := by
  cases query with
  | inl request => exact sparseDraw_bound request state
  | inr request =>
      rw [combinedDraw, externalDraw, drawBound_map]
      exact sparseDraw_bound (.read request) state

/-- The list stores each reached update to the permutation family. -/
abbrev FamilyHistory := List (OracleIndex × ProgrammedPermutation (2 ^ 128))

/-- The finite lookup implementation never enumerates the oracle index type. -/
def lookupFamily : FamilyHistory → OracleIndex → ProgrammedPermutation (2 ^ 128)
  | [], _ => ProgrammedPermutation.empty _
  | entry :: rest, index => if index = entry.1 then entry.2 else lookupFamily rest index

/-- The counted lookup visits only the stored update list. -/
def lookupFamilyCost : FamilyHistory → OracleIndex → ProgrammedPermutation (2 ^ 128) × Nat
  | [], _ => (ProgrammedPermutation.empty _, 0)
  | entry :: rest, index =>
      if index = entry.1 then (entry.2, 1)
      else let answer := lookupFamilyCost rest index; (answer.1, answer.2 + 1)

theorem lookupFamilyCost_correct (history : FamilyHistory) (index : OracleIndex) :
    (lookupFamilyCost history index).1 = lookupFamily history index := by
  induction history with
  | nil => rfl
  | cons entry rest ih => simp only [lookupFamilyCost, lookupFamily]; split <;> simp_all

theorem lookupFamilyCost_le (history : FamilyHistory) (index : OracleIndex) :
    (lookupFamilyCost history index).2 ≤ history.length := by
  induction history with
  | nil => simp [lookupFamilyCost]
  | cons entry rest ih => simp only [lookupFamilyCost]; split <;> simp_all

/-- Prepending one record implements the actual function update. -/
theorem lookupFamily_cons (history : FamilyHistory) (index : OracleIndex)
    (value : ProgrammedPermutation (2 ^ 128)) :
    lookupFamily ((index, value) :: history) = Function.update (lookupFamily history) index value := by
  funext query
  by_cases same : query = index
  · subst query; simp [lookupFamily]
  · simp [lookupFamily, same]

/-- The resource certificate supplies a finite implementation of the family function. -/
structure OracleBound (oracles : OracleData) (capacity : Nat) where
  history : FamilyHistory
  represented : oracles.1 = lookupFamily history
  historyLength : history.length ≤ capacity
  localBounds : ∀ index, (oracles.1 index).base.used ≤ capacity ∧
    (oracles.1 index).overlay.length ≤ capacity
  hashLength : oracles.2.length ≤ capacity

/-- The state bound includes every oracle transcript length. -/
structure StateBound (state : SparseState) (capacity : Nat) extends OracleBound state.oracles capacity where
  fixedLength : state.metadata.fixedTranscript.length ≤ capacity
  encLength : state.metadata.encTranscript.length ≤ capacity
  hashTranscriptLength : state.metadata.hashTranscript.length ≤ capacity

def OracleBound.mono {oracles : OracleData} {first second : Nat}
    (bound : OracleBound oracles first) (larger : first ≤ second) : OracleBound oracles second where
  history := bound.history
  represented := bound.represented
  historyLength := bound.historyLength.trans larger
  localBounds := fun index => ⟨(bound.localBounds index).1.trans larger,
    (bound.localBounds index).2.trans larger⟩
  hashLength := bound.hashLength.trans larger

def StateBound.mono {state : SparseState} {first second : Nat}
    (bound : StateBound state first) (larger : first ≤ second) : StateBound state second where
  toOracleBound := bound.toOracleBound.mono larger
  fixedLength := bound.fixedLength.trans larger
  encLength := bound.encLength.trans larger
  hashTranscriptLength := bound.hashTranscriptLength.trans larger

/-- The selected family lookup has a verified finite scan bound. -/
theorem OracleBound.lookup_cost {oracles : OracleData} {capacity : Nat}
    (bound : OracleBound oracles capacity) (index : OracleIndex) :
    (lookupFamilyCost bound.history index).1 = oracles.1 index ∧
      (lookupFamilyCost bound.history index).2 ≤ capacity := by
  constructor
  · rw [lookupFamilyCost_correct, bound.represented]
  · exact (lookupFamilyCost_le _ _).trans bound.historyLength

/-- One family update preserves the resource certificate. -/
def OracleBound.update {oracles : OracleData} {capacity : Nat}
    (bound : OracleBound oracles capacity) (index : OracleIndex)
    (value : ProgrammedPermutation (2 ^ 128))
    (used : value.base.used ≤ capacity + 1) (overlay : value.overlay.length ≤ capacity + 1) :
    OracleBound (Function.update oracles.1 index value, oracles.2) (capacity + 1) where
  history := (index, value) :: bound.history
  represented := by simp only [lookupFamily_cons, bound.represented]
  historyLength := Nat.succ_le_succ bound.historyLength
  localBounds := by
    intro query
    by_cases same : query = index
    · subst query; simpa using And.intro used overlay
    · simp only [Function.update_of_ne same]
      exact ⟨(bound.localBounds query).1.trans (Nat.le_succ _),
        (bound.localBounds query).2.trans (Nat.le_succ _)⟩
  hashLength := bound.hashLength.trans (Nat.le_succ _)

/-- One hash update preserves the family representation. -/
def OracleBound.updateHash {oracles : OracleData} {capacity : Nat}
    (bound : OracleBound oracles capacity) (table : HashTable BaseField (2 ^ 256))
    (length : table.length ≤ capacity + 1) : OracleBound (oracles.1, table) (capacity + 1) where
  history := bound.history
  represented := bound.represented
  historyLength := bound.historyLength.trans (Nat.le_succ _)
  localBounds := fun index => ⟨(bound.localBounds index).1.trans (Nat.le_succ _),
    (bound.localBounds index).2.trans (Nat.le_succ _)⟩
  hashLength := length

/-- Every local family operation adds at most one base pair and one overlay entry. -/
theorem family_local_resources (action : ProgramAction (2 ^ 128))
    (selected : ProgrammedPermutation (2 ^ 128))
    (answer : Fin (2 ^ 128) × ProgrammedPermutation (2 ^ 128))
    (reached : answer ∈ (programSampled action selected).support) :
    answer.2.base.used ≤ selected.base.used + 1 ∧
      answer.2.overlay.length ≤ selected.overlay.length + 1 := by
  cases action with
  | forward input =>
      obtain ⟨used, overlay⟩ := selected.forward_resources input answer reached
      exact ⟨used, by rw [overlay]; exact Nat.le_succ _⟩
  | inverse output =>
      obtain ⟨used, overlay⟩ := selected.inverse_resources output answer reached
      exact ⟨used, by rw [overlay]; exact Nat.le_succ _⟩
  | program input target =>
      obtain ⟨next, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      rw [← same]
      obtain ⟨used, overlay⟩ := selected.program_resources input target next member
      exact ⟨used, Nat.le_of_eq overlay⟩

/-- Every reached lower request retains a finite family and bounded sparse tables. -/
theorem lower_resources (query : lowerSpec.Query) (oracles : OracleData) (capacity : Nat)
    (bound : OracleBound oracles capacity)
    (answer : lowerSpec.Answer query × OracleData)
    (reached : answer ∈ (lowerDraw query oracles).distribution.support) :
    Nonempty (OracleBound answer.2 (capacity + 1)) := by
  cases query with
  | inl request =>
      rw [lowerDraw, Draw.map_distribution] at reached
      obtain ⟨familyAnswer, familyReached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      rw [← same]
      rw [familyDraw_distribution] at familyReached
      change familyAnswer ∈ ((programSampled request.2 (oracles.1 request.1)).map
        (fun output => (output.1, Function.update oracles.1 request.1 output.2))).support at familyReached
      obtain ⟨localAnswer, localReached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp familyReached
      rw [← same]
      have localFact := family_local_resources request.2 (oracles.1 request.1) localAnswer localReached
      exact ⟨bound.update request.1 localAnswer.2
        (localFact.1.trans (Nat.add_le_add_right (bound.localBounds request.1).1 1))
        (localFact.2.trans (Nat.add_le_add_right (bound.localBounds request.1).2 1))⟩
  | inr key =>
      rw [lowerDraw, Draw.map_distribution] at reached
      obtain ⟨hashAnswer, hashReached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      rw [← same]
      have length := oracles.2.query_length_le (by norm_num : 0 < 2 ^ 256) key hashAnswer hashReached
      exact ⟨bound.updateHash hashAnswer.2 (length.trans (Nat.add_le_add_right bound.hashLength 1))⟩

/-- Internal reads preserve all metadata bounds. -/
def StateBound.readOracles {state : SparseState} {capacity : Nat}
    (bound : StateBound state capacity) (oracles : OracleData)
    (oracleBound : OracleBound oracles (capacity + 1)) :
    StateBound { state with oracles := oracles } (capacity + 1) where
  toOracleBound := oracleBound
  fixedLength := bound.fixedLength.trans (Nat.le_succ _)
  encLength := bound.encLength.trans (Nat.le_succ _)
  hashTranscriptLength := bound.hashTranscriptLength.trans (Nat.le_succ _)

/-- Successful programming adds exactly one fixed transcript entry. -/
def StateBound.programOracles {state : SparseState} {capacity : Nat}
    (bound : StateBound state capacity) (command : FixedCommand) (oracles : OracleData)
    (oracleBound : OracleBound oracles (capacity + 1)) :
    StateBound { oracles := oracles, metadata := state.metadata.program command } (capacity + 1) where
  toOracleBound := oracleBound
  fixedLength := Nat.succ_le_succ bound.fixedLength
  encLength := bound.encLength.trans (Nat.le_succ _)
  hashTranscriptLength := bound.hashTranscriptLength.trans (Nat.le_succ _)

/-- A failed programming attempt changes only the bad flag. -/
def StateBound.markBad {state : SparseState} {capacity : Nat}
    (bound : StateBound state capacity) :
    StateBound { state with metadata := state.metadata.markBad } (capacity + 1) where
  toOracleBound := bound.toOracleBound.mono (Nat.le_succ _)
  fixedLength := bound.fixedLength.trans (Nat.le_succ _)
  encLength := bound.encLength.trans (Nat.le_succ _)
  hashTranscriptLength := bound.hashTranscriptLength.trans (Nat.le_succ _)

/-- The actual sparse machine increases each resource bound by at most one. -/
theorem sparse_resources (request : spec.Query) (state : SparseState) (capacity : Nat)
    (bound : StateBound state capacity) (answer : spec.Answer request × SparseState)
    (reached : answer ∈ (sparseDraw request state).distribution.support) :
    Nonempty (StateBound answer.2 (capacity + 1)) := by
  cases request with
  | read query =>
      rw [sparseDraw, Draw.map_distribution] at reached
      obtain ⟨lowerAnswer, lowerReached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      rw [← same]
      obtain ⟨oracleBound⟩ := lower_resources (lowerRequest (.read query)) state.oracles capacity
        bound.toOracleBound lowerAnswer lowerReached
      exact ⟨bound.readOracles lowerAnswer.2 oracleBound⟩
  | program command =>
      unfold sparseDraw at reached
      dsimp only at reached
      split at reached
      · rw [Draw.map_distribution] at reached
        obtain ⟨lowerAnswer, lowerReached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
        rw [← same]
        obtain ⟨oracleBound⟩ := lower_resources (lowerRequest (.program command)) state.oracles capacity
          bound.toOracleBound lowerAnswer lowerReached
        exact ⟨bound.programOracles command lowerAnswer.2 oracleBound⟩
      · simp only [Draw.distribution, PMF.mem_support_pure_iff] at reached
        rw [reached]
        exact ⟨bound.markBad⟩

/-- An external query appends one entry to exactly one public transcript. -/
def StateBound.recordOracles {state : SparseState} {capacity : Nat}
    (bound : StateBound state capacity) (query : Garbling.OracleQuery)
    (answer : Garbling.OracleAnswer query) (oracles : OracleData)
    (oracleBound : OracleBound oracles (capacity + 1)) :
    StateBound { oracles := oracles, metadata := state.metadata.record query answer } (capacity + 1) where
  toOracleBound := oracleBound
  fixedLength := by
    cases query <;> simp only [Metadata.record, List.length_cons]
    all_goals first | exact Nat.succ_le_succ bound.fixedLength | exact bound.fixedLength.trans (Nat.le_succ _)
  encLength := by
    cases query <;> simp only [Metadata.record, List.length_cons]
    all_goals first | exact Nat.succ_le_succ bound.encLength | exact bound.encLength.trans (Nat.le_succ _)
  hashTranscriptLength := by
    cases query <;> simp only [Metadata.record, List.length_cons]
    all_goals first | exact Nat.succ_le_succ bound.hashTranscriptLength |
      exact bound.hashTranscriptLength.trans (Nat.le_succ _)

/-- Every reached external query preserves the finite representation and transcript bounds. -/
theorem external_resources (query : Garbling.OracleQuery) (state : SparseState) (capacity : Nat)
    (bound : StateBound state capacity) (answer : Garbling.OracleAnswer query × SparseState)
    (reached : answer ∈ (externalDraw query state).distribution.support) :
    Nonempty (StateBound answer.2 (capacity + 1)) := by
  rw [externalDraw, Draw.map_distribution, sparseDraw, Draw.map_distribution, PMF.map_comp] at reached
  obtain ⟨lowerAnswer, lowerReached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  rw [← same]
  obtain ⟨oracleBound⟩ := lower_resources (lowerRequest (.read query)) state.oracles capacity
    bound.toOracleBound lowerAnswer lowerReached
  exact ⟨bound.recordOracles query (SimulatorMachine.lowerAnswer (.read query) lowerAnswer.1)
    lowerAnswer.2 oracleBound⟩

/-- Internal operations and external queries share the same resource bound. -/
theorem combined_resources (query : combinedSpec.Query) (state : SparseState) (capacity : Nat)
    (bound : StateBound state capacity) (answer : combinedSpec.Answer query × SparseState)
    (reached : answer ∈ (combinedDraw query state).distribution.support) :
    Nonempty (StateBound answer.2 (capacity + 1)) := by
  cases query with
  | inl request => exact sparse_resources request state capacity bound answer reached
  | inr request => exact external_resources request state capacity bound answer reached

/-- The lower charge includes the index scan, permutation tests, hash scan, and overlay append. -/
def lowerCharge (depth : Nat) (query : lowerSpec.Query) (oracles : OracleData) : Nat :=
  match query with
  | .inl (index, action) =>
      let selected := oracles.1 index
      depth + selected.queryComparisons +
        (match action with | .program _ _ => selected.overlay.length | _ => 0) + 4
  | .inr _ => oracles.2.length + 4

/-- The machine charge also includes the actual metadata freshness scan. -/
def charge (depth : Nat) (request : spec.Query) (state : SparseState) : Nat :=
  match request with
  | .read _ => lowerCharge depth (lowerRequest request) state.oracles + 8
  | .program command =>
      let checked := checkFixedCost state.metadata.fixedTranscript command
      checked.2 + if checked.1 then lowerCharge depth (lowerRequest request) state.oracles + 8 else 1

theorem lowerCharge_le (depth capacity : Nat) (query : lowerSpec.Query) (oracles : OracleData)
    (bound : OracleBound oracles capacity) (depthBound : depth ≤ capacity) :
    lowerCharge depth query oracles ≤ 8 * capacity + 4 := by
  cases query with
  | inl request =>
      rcases request with ⟨index, action⟩
      obtain ⟨used, overlay⟩ := bound.localBounds index
      have comparisons := (oracles.1 index).queryComparisons_le
      cases action <;> simp only [lowerCharge] <;> omega
  | inr key =>
      have length := bound.hashLength
      simp only [lowerCharge]
      omega

/-- Failed programming attempts also satisfy the concrete scan bound. -/
theorem charge_le (depth capacity : Nat) (request : spec.Query) (state : SparseState)
    (bound : StateBound state capacity) (depthBound : depth ≤ capacity) :
    charge depth request state ≤ 10 * capacity + 16 := by
  have lower := lowerCharge_le depth capacity (lowerRequest request) state.oracles
    bound.toOracleBound depthBound
  cases request with
  | read query => simp only [charge]; omega
  | program command =>
      have check := checkFixedCost_le state.metadata.fixedTranscript command
      have length := bound.fixedLength
      simp only [charge]
      split <;> omega

/-- External operations also charge their transcript insertion. -/
def combinedCharge (depth : Nat) (query : combinedSpec.Query) (state : SparseState) : Nat :=
  match query with
  | .inl request => charge depth request state
  | .inr request => lowerCharge depth (lowerRequest (.read request)) state.oracles + 9

theorem combinedCharge_le (depth capacity : Nat) (query : combinedSpec.Query) (state : SparseState)
    (bound : StateBound state capacity) (depthBound : depth ≤ capacity) :
    combinedCharge depth query state ≤ 10 * capacity + 16 := by
  cases query with
  | inl request => exact charge_le depth capacity request state bound depthBound
  | inr request =>
      have lower := lowerCharge_le depth capacity (lowerRequest (.read request)) state.oracles
        bound.toOracleBound depthBound
      simp only [combinedCharge]
      omega

/-- Every concrete bounded-integer source selects a supported draw result. -/
theorem runDraw_support {A Seed : Type}
    (random : (size : Nat) → 0 < size → Seed → Fin size × Seed)
    (draw : Draw A) (seed : Seed) :
    (runDraw random draw seed).1 ∈ draw.distribution.support := by
  cases draw with
  | pure value => simp only [runDraw, Draw.distribution, PMF.mem_support_pure_iff]
  | uniform size positive next =>
      let : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
      apply (PMF.mem_support_map_iff _ _ _).mpr
      exact ⟨(random size positive seed).1, PMF.mem_support_uniformOfFintype _, rfl⟩

/-- The counted interpreter executes the same sparse operations and accumulates their charges. -/
def executeCost {A Seed : Type} {budget : Nat}
    (random : (size : Nat) → 0 < size → Seed → Fin size × Seed) :
    Program combinedSpec A budget → SparseState → Seed → Nat →
      (A × SparseState × Seed) × Nat × Nat
  | .pure value, state, seed, _ => ((value, state, seed), 0, 0)
  | .query query next, state, seed, depth =>
      let answer := runDraw random (combinedDraw query state) seed
      let tail := executeCost random (next answer.1.1) answer.1.2 answer.2 (depth + 1)
      (tail.1, tail.2.1 + 1, combinedCharge depth query state + tail.2.2)
  | .map f source, state, seed, depth =>
      let answer := executeCost random source state seed depth
      ((f answer.1.1, answer.1.2), answer.2)
  | .bind source next, state, seed, depth =>
      let first := executeCost random source state seed depth
      let second := executeCost random (next first.1.1) first.1.2.1 first.1.2.2 (depth + first.2.1)
      (second.1, first.2.1 + second.2.1, first.2.2 + second.2.2)
  | .weaken source _, state, seed, depth => executeCost random source state seed depth

/-- The cost instrumentation preserves the exact result, state, seed, and operation count. -/
theorem executeCost_correct {A Seed : Type} {budget : Nat}
    (random : (size : Nat) → 0 < size → Seed → Fin size × Seed)
    (program : Program combinedSpec A budget) (state : SparseState) (seed : Seed) (depth : Nat) :
    (executeCost random program state seed depth).1 = program.execute combinedDraw random state seed ∧
      (executeCost random program state seed depth).2.1 =
        (program.runCount (randomHandler combinedDraw random) (state, seed)).2 := by
  induction program generalizing state seed depth with
  | pure => exact ⟨rfl, rfl⟩
  | query query next ih =>
      have tail := ih (runDraw random (combinedDraw query state) seed).1.1
        (runDraw random (combinedDraw query state) seed).1.2
        (runDraw random (combinedDraw query state) seed).2 (depth + 1)
      exact ⟨tail.1, congrArg (fun n => n + 1) tail.2⟩
  | map f source ih =>
      obtain ⟨same, calls⟩ := ih state seed depth
      constructor
      · simp only [executeCost, Program.execute, Program.run] at same ⊢
        rw [same]
      · exact calls
  | bind source next first second =>
      obtain ⟨firstEq, firstCalls⟩ := first state seed depth
      obtain ⟨secondEq, secondCalls⟩ := second (executeCost random source state seed depth).1.1
        (executeCost random source state seed depth).1.2.1
        (executeCost random source state seed depth).1.2.2
        (depth + (executeCost random source state seed depth).2.1)
      constructor
      · simp only [executeCost]
        rw [secondEq, firstEq]
        rfl
      · simp only [executeCost, Program.runCount]
        rw [secondCalls, firstCalls, firstEq,
          (Program.runCount_correct (randomHandler combinedDraw random) source (state, seed)).1]
        rfl
  | weaken source bounded ih => exact ih state seed depth

/-- Every execution keeps a finite resource certificate and a quadratic total charge. -/
theorem executeCost_resources {A Seed : Type} {budget : Nat}
    (random : (size : Nat) → 0 < size → Seed → Fin size × Seed)
    (program : Program combinedSpec A budget) (state : SparseState) (seed : Seed)
    (depth capacity : Nat) (bound : StateBound state capacity) (depthBound : depth ≤ capacity) :
    Nonempty (StateBound (executeCost random program state seed depth).1.2.1
      (capacity + (executeCost random program state seed depth).2.1)) ∧
      (executeCost random program state seed depth).2.2 ≤
        (executeCost random program state seed depth).2.1 *
          (10 * (capacity + (executeCost random program state seed depth).2.1) + 16) := by
  induction program generalizing state seed depth capacity with
  | pure value => exact ⟨⟨bound⟩, by simp [executeCost]⟩
  | query query next ih =>
      let answer := runDraw random (combinedDraw query state) seed
      let tail := executeCost random (next answer.1.1) answer.1.2 answer.2 (depth + 1)
      obtain ⟨nextBound⟩ := combined_resources query state capacity bound answer.1
        (runDraw_support random (combinedDraw query state) seed)
      obtain ⟨finalBound, tailCost⟩ := ih answer.1.1 answer.1.2 answer.2 (depth + 1) (capacity + 1)
        nextBound (Nat.add_le_add_right depthBound 1)
      change Nonempty (StateBound tail.1.2.1 (capacity + (tail.2.1 + 1))) ∧
        combinedCharge depth query state + tail.2.2 ≤
          (tail.2.1 + 1) * (10 * (capacity + (tail.2.1 + 1)) + 16)
      constructor
      · have order : capacity + 1 + tail.2.1 = capacity + (tail.2.1 + 1) := by omega
        rw [← order]
        exact finalBound
      · have stepCost := combinedCharge_le depth capacity query state bound depthBound
        change tail.2.2 ≤ tail.2.1 * (10 * (capacity + 1 + tail.2.1) + 16) at tailCost
        nlinarith
  | map f source ih => exact ih state seed depth capacity bound depthBound
  | bind source next first second =>
      let firstResult := executeCost random source state seed depth
      let secondResult := executeCost random (next firstResult.1.1) firstResult.1.2.1
        firstResult.1.2.2 (depth + firstResult.2.1)
      obtain ⟨⟨middleBound⟩, firstCost⟩ := first state seed depth capacity bound depthBound
      obtain ⟨finalBound, secondCost⟩ := second firstResult.1.1 firstResult.1.2.1 firstResult.1.2.2
        (depth + firstResult.2.1) (capacity + firstResult.2.1) middleBound
        (Nat.add_le_add_right depthBound firstResult.2.1)
      change Nonempty (StateBound secondResult.1.2.1 (capacity + (firstResult.2.1 + secondResult.2.1))) ∧
        firstResult.2.2 + secondResult.2.2 ≤
          (firstResult.2.1 + secondResult.2.1) *
            (10 * (capacity + (firstResult.2.1 + secondResult.2.1)) + 16)
      constructor
      · rw [← Nat.add_assoc]
        exact finalBound
      · change firstResult.2.2 ≤ firstResult.2.1 * (10 * (capacity + firstResult.2.1) + 16) at firstCost
        change secondResult.2.2 ≤ secondResult.2.1 *
          (10 * (capacity + firstResult.2.1 + secondResult.2.1) + 16) at secondCost
        nlinarith [Nat.zero_le (firstResult.2.1 * secondResult.2.1)]
  | weaken source bounded ih => exact ih state seed depth capacity bound depthBound

/-- The actual operation budget bounds the full charged execution cost. -/
theorem executeCost_budget {A Seed : Type} {budget : Nat}
    (random : (size : Nat) → 0 < size → Seed → Fin size × Seed)
    (program : Program combinedSpec A budget) (state : SparseState) (seed : Seed)
    (depth capacity : Nat) (bound : StateBound state capacity) (depthBound : depth ≤ capacity) :
    (executeCost random program state seed depth).2.1 ≤ budget ∧
      (executeCost random program state seed depth).2.2 ≤ budget * (10 * (capacity + budget) + 16) := by
  have calls := (Program.execute_calls combinedDraw random program state seed).2
  rw [← (executeCost_correct random program state seed depth).2] at calls
  constructor
  · exact calls
  · have cost := (executeCost_resources random program state seed depth capacity bound depthBound).2
    exact cost.trans (Nat.mul_le_mul calls (by omega))

/-- The resource theorem applies to the production executable result and every random tape. -/
theorem execute_resources {A Seed : Type} {budget : Nat}
    (random : (size : Nat) → 0 < size → Seed → Fin size × Seed)
    (program : Program combinedSpec A budget) (state : SparseState) (seed : Seed)
    (depth capacity : Nat) (bound : StateBound state capacity) (depthBound : depth ≤ capacity) :
    Nonempty (StateBound (program.execute combinedDraw random state seed).2.1 (capacity + budget)) := by
  obtain ⟨finalBound⟩ := (executeCost_resources random program state seed depth capacity bound depthBound).1
  have calls := (executeCost_budget random program state seed depth capacity bound depthBound).1
  have larger := finalBound.mono (Nat.add_le_add_left calls capacity)
  rw [(executeCost_correct random program state seed depth).1] at larger
  exact ⟨larger⟩

/-- Empty sparse oracles require no initial family lookup or hash storage. -/
def initialBound (metadata : Metadata) (capacity : Nat)
    (fixed : metadata.fixedTranscript.length ≤ capacity)
    (enc : metadata.encTranscript.length ≤ capacity)
    (hash : metadata.hashTranscript.length ≤ capacity) :
    StateBound ⟨((fun _ => ProgrammedPermutation.empty _), []), metadata⟩ capacity where
  history := []
  represented := rfl
  historyLength := Nat.zero_le _
  localBounds := fun _ => ⟨Nat.zero_le _, Nat.zero_le _⟩
  hashLength := Nat.zero_le _
  fixedLength := fixed
  encLength := enc
  hashTranscriptLength := hash

end Cost
end SimulatorMachine
end Kriterion.ArgoMAC.Security
