import Cryptography.Permutation
import ToMathlib.Probability.ProbabilityMassFunction.Lemmas
import Mathlib.Tactic

namespace Kriterion.ArgoMAC.Security.OperationalOracle
open Cryptography
/-- A step draws at most one uniform bounded integer. -/
inductive Draw (A : Type) where
  | pure (value : A)
  | uniform (bound : Nat) (positive : 0 < bound) (next : Fin bound → A)

noncomputable def Draw.distribution {A : Type} : Draw A → PMF A
  | .pure value => PMF.pure value
  | .uniform bound positive next =>
      letI : Nonempty (Fin bound) := ⟨⟨0, positive⟩⟩
      (PMF.uniformOfFintype (Fin bound)).map next

def Draw.map {A B : Type} (f : A → B) : Draw A → Draw B
  | .pure value => .pure (f value)
  | .uniform bound positive next => .uniform bound positive (f ∘ next)

theorem Draw.map_distribution {A B : Type} (draw : Draw A) (f : A → B) :
    (draw.map f).distribution = draw.distribution.map f := by
  cases draw <;> simp [map, distribution, PMF.map_comp, PMF.pure_map]

/-- This function applies only the stored transpositions. -/
def swaps {A : Type} [DecidableEq A] : List (A × A) → Equiv.Perm A
  | [] => Equiv.refl A
  | pair :: rest => (Equiv.swap pair.1 pair.2).trans (swaps rest)

@[simp] theorem swaps_nil {A : Type} [DecidableEq A] :
    swaps ([] : List (A × A)) = Equiv.refl A := rfl

@[simp] theorem swaps_cons {A : Type} [DecidableEq A]
    (pair : A × A) (rest : List (A × A)) (a : A) :
    swaps (pair :: rest) a = swaps rest (Equiv.swap pair.1 pair.2 a) := rfl

theorem swaps_append {A : Type} [DecidableEq A]
    (first second : List (A × A)) :
    swaps (first ++ second) = (swaps first).trans (swaps second) := by
  induction first with
  | nil => rfl
  | cons pair rest ih =>
      apply Equiv.ext
      intro a
      simp only [List.cons_append, swaps_cons, Equiv.trans_apply, ih]


/-- The two sparse permutations pair the used input and output prefixes. -/
structure SparsePermutation (size : Nat) where
  used : Nat
  within : used ≤ size
  inputs : List (Fin size × Fin size)
  outputs : List (Fin size × Fin size)
  inputLength : inputs.length ≤ used
  outputLength : outputs.length ≤ used

def SparsePermutation.empty (size : Nat) : SparsePermutation size :=
  ⟨0, Nat.zero_le _, [], [], by simp, by simp⟩

def SparsePermutation.input {size : Nat} (state : SparsePermutation size) :
    Equiv.Perm (Fin size) := swaps state.inputs

def SparsePermutation.output {size : Nat} (state : SparsePermutation size) :
    Equiv.Perm (Fin size) := swaps state.outputs

def SparsePermutation.knownInput {size : Nat} (state : SparsePermutation size)
    (x : Fin size) : Prop := (state.input.symm x).val < state.used

def SparsePermutation.knownOutput {size : Nat} (state : SparsePermutation size)
    (y : Fin size) : Prop := (state.output.symm y).val < state.used

instance {size : Nat} (state : SparsePermutation size) (x : Fin size) :
    Decidable (state.knownInput x) := inferInstanceAs (Decidable (_ < _))

instance {size : Nat} (state : SparsePermutation size) (y : Fin size) :
    Decidable (state.knownOutput y) := inferInstanceAs (Decidable (_ < _))

/-- The rank selects one unused position without rejection. -/
def SparsePermutation.suffix {size : Nat} (state : SparsePermutation size)
    (rank : Fin (size - state.used)) : Fin size :=
  ⟨state.used + rank.val, by have := rank.isLt; omega⟩

/-- The update adds one pair to the partial permutation. -/
def SparsePermutation.extend {size : Nat} (state : SparsePermutation size)
    (room : state.used < size) (inputPosition outputPosition : Fin size) :
    SparsePermutation size where
  used := state.used + 1
  within := by omega
  inputs := (⟨state.used, room⟩, inputPosition) :: state.inputs
  outputs := (⟨state.used, room⟩, outputPosition) :: state.outputs
  inputLength := by simpa using Nat.succ_le_succ state.inputLength
  outputLength := by simpa using Nat.succ_le_succ state.outputLength

/-- A forward query samples only when its input is new. -/
def SparsePermutation.forward {size : Nat} (state : SparsePermutation size)
    (x : Fin size) : Draw (Fin size × SparsePermutation size) :=
  let position := state.input.symm x
  if known : position.val < state.used then
    .pure (state.output position, state)
  else
    .uniform (size - state.used) (by have := position.isLt; omega) fun rank =>
      let chosen := state.suffix rank
      (state.output chosen,
        state.extend (by have := position.isLt; omega) position chosen)

/-- An inverse query uses the same partial permutation. -/
def SparsePermutation.inverse {size : Nat} (state : SparsePermutation size)
    (y : Fin size) : Draw (Fin size × SparsePermutation size) :=
  let position := state.output.symm y
  if known : position.val < state.used then
    .pure (state.input position, state)
  else
    .uniform (size - state.used) (by have := position.isLt; omega) fun rank =>
      let chosen := state.suffix rank
      (state.input chosen,
        state.extend (by have := position.isLt; omega) chosen position)

/-- This bound counts comparisons in both transposition lists. -/
def SparsePermutation.lookupComparisons {size : Nat} (state : SparsePermutation size) : Nat :=
  2 * (state.inputs.length + state.outputs.length)

theorem SparsePermutation.lookupComparisons_le {size : Nat}
    (state : SparsePermutation size) : state.lookupComparisons ≤ 4 * state.used := by
  have := state.inputLength
  have := state.outputLength
  simp only [lookupComparisons]
  omega

/-- The unused ranks enumerate exactly the unused outputs. -/
def SparsePermutation.unusedOutputEquiv {size : Nat} (state : SparsePermutation size) :
    Fin (size - state.used) ≃ {y : Fin size // ¬ state.knownOutput y} where
  toFun rank := ⟨state.output (state.suffix rank), by
    simp [knownOutput, suffix]⟩
  invFun y := ⟨(state.output.symm y.val).val - state.used, by
    have h := (state.output.symm y.val).isLt
    have h' : ¬ (state.output.symm y.val).val < state.used := y.property
    omega⟩
  left_inv rank := by
    apply Fin.ext
    simp [suffix]
  right_inv y := by
    apply Subtype.ext
    apply state.output.symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Fin.ext
    have h' : ¬ (state.output.symm y.val).val < state.used := y.property
    simp only [suffix]
    omega

/-- The integer sampler gives the exact uniform unused-output law. -/
theorem SparsePermutation.unusedOutput_uniform {size : Nat}
    (state : SparsePermutation size) (room : state.used < size) :
    letI : Nonempty (Fin (size - state.used)) := ⟨⟨0, by omega⟩⟩
    letI : Nonempty {y : Fin size // ¬ state.knownOutput y} :=
      ⟨state.unusedOutputEquiv ⟨0, by omega⟩⟩
    (PMF.uniformOfFintype (Fin (size - state.used))).map
        state.unusedOutputEquiv =
      PMF.uniformOfFintype {y : Fin size // ¬ state.knownOutput y} := by
  letI : Nonempty (Fin (size - state.used)) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty {y : Fin size // ¬ state.knownOutput y} :=
    ⟨state.unusedOutputEquiv ⟨0, by omega⟩⟩
  exact PMF.uniformOfFintype_map_of_bijective _ state.unusedOutputEquiv.bijective


/-- The update preserves each earlier pair. -/
theorem SparsePermutation.extend_old {size : Nat}
    (state : SparsePermutation size) (room : state.used < size)
    (inputPosition outputPosition position : Fin size)
    (old : position.val < state.used)
    (freshInput : state.used ≤ inputPosition.val)
    (freshOutput : state.used ≤ outputPosition.val) :
    let next := state.extend room inputPosition outputPosition
    next.input position = state.input position ∧
      next.output position = state.output position := by
  have different : position ≠ (⟨state.used, room⟩ : Fin size) := by
    intro eq
    have h : position.val = state.used := congrArg Fin.val eq
    omega
  have inputDifferent : position ≠ inputPosition := by
    intro eq; have := congrArg Fin.val eq; omega
  have outputDifferent : position ≠ outputPosition := by
    intro eq; have := congrArg Fin.val eq; omega
  simp [extend, input, output, swaps, Equiv.swap_apply_of_ne_of_ne,
    different, inputDifferent, outputDifferent]

/-- The overlay stores each output swap instead of changing a full oracle. -/
def programOverlay {A : Type} (overlay : List (A × A)) (current target : A) :
    List (A × A) := overlay ++ [(current, target)]

/-- The overlay implements the same permutation on every input. -/
theorem programOverlay_exact {A : Type} [DecidableEq A]
    (base : Equiv.Perm A) (overlay : List (A × A)) (input target : A) :
    base.trans (swaps (programOverlay overlay (swaps overlay (base input)) target)) =
      (base.trans (swaps overlay)).trans
        (Equiv.swap ((base.trans (swaps overlay)) input) target) := by
  rw [programOverlay, swaps_append]
  rfl

/-- The overlay adds one stored transposition. -/
theorem programOverlay_length {A : Type} (overlay : List (A × A)) (current target : A) :
    (programOverlay overlay current target).length = overlay.length + 1 := by
  simp [programOverlay]


/-- The sparse prefixes define the exact partial assignment. -/
def SparsePermutation.assignment {size : Nat} (state : SparsePermutation size) :
    {x : Fin size // state.knownInput x} ≃ {y : Fin size // state.knownOutput y} where
  toFun x := ⟨state.output (state.input.symm x.val), by
    simpa only [knownOutput, knownInput, Equiv.symm_apply_apply] using x.property⟩
  invFun y := ⟨state.input (state.output.symm y.val), by
    simpa only [knownInput, knownOutput, Equiv.symm_apply_apply] using y.property⟩
  left_inv x := by simp
  right_inv y := by simp

/-- This type contains the eager permutations consistent with the sparse state. -/
abbrev SparsePermutation.Completion {size : Nat} (state : SparsePermutation size) :=
  {π : Equiv.Perm (Fin size) //
    ∀ x : {x : Fin size // state.knownInput x}, π x = state.assignment x}

noncomputable instance {size : Nat} (state : SparsePermutation size) :
    Fintype state.Completion := by
  classical
  unfold SparsePermutation.Completion
  infer_instance

instance {size : Nat} (state : SparsePermutation size) : Nonempty state.Completion :=
  ⟨⟨state.input.symm.trans state.output, fun _ => rfl⟩⟩

/-- Prefix coordinates give the same compatibility condition. -/
theorem SparsePermutation.completion_iff {size : Nat} (state : SparsePermutation size)
    (π : Equiv.Perm (Fin size)) :
    (∀ x : {x : Fin size // state.knownInput x}, π x = state.assignment x) ↔
      ∀ position : Fin size, position.val < state.used →
        π (state.input position) = state.output position := by
  constructor
  · intro compatible position known
    have member : state.knownInput (state.input position) := by
      simpa only [knownInput, Equiv.symm_apply_apply] using known
    simpa only [assignment, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using
      compatible ⟨state.input position, member⟩
  · intro compatible x
    simpa only [assignment, Equiv.coe_fn_mk, Equiv.apply_symm_apply] using
      compatible (state.input.symm x.val) x.property

/-- A fresh extension adds exactly one equation to the completion fiber. -/
theorem SparsePermutation.extend_completion_iff {size : Nat}
    (state : SparsePermutation size) (room : state.used < size)
    (inputPosition outputPosition : Fin size)
    (freshInput : state.used ≤ inputPosition.val)
    (freshOutput : state.used ≤ outputPosition.val)
    (π : Equiv.Perm (Fin size)) :
    (∀ x : {x : Fin size // (state.extend room inputPosition outputPosition).knownInput x},
      π x = (state.extend room inputPosition outputPosition).assignment x) ↔
      (∀ x : {x : Fin size // state.knownInput x}, π x = state.assignment x) ∧
        π (state.input inputPosition) = state.output outputPosition := by
  rw [SparsePermutation.completion_iff, SparsePermutation.completion_iff]
  constructor
  · intro compatible
    constructor
    · intro position old
      have preserved := state.extend_old room inputPosition outputPosition position
        old freshInput freshOutput
      have eq := compatible position (by simp only [extend]; omega)
      rw [preserved.1, preserved.2] at eq
      exact eq
    · have eq := compatible ⟨state.used, room⟩ (by simp [extend])
      simpa [extend, input, output, swaps] using eq
  · rintro ⟨compatible, pair⟩ position member
    have member' : position.val < state.used + 1 := member
    by_cases old : position.val < state.used
    · have preserved := state.extend_old room inputPosition outputPosition position
        old freshInput freshOutput
      rw [preserved.1, preserved.2]
      exact compatible position old
    · have same : position = ⟨state.used, room⟩ := by
        apply Fin.ext
        change position.val = state.used
        omega
      subst position
      simpa [extend, input, output, swaps] using pair

/-- The sparse update preserves the full conditional eager fiber. -/
def SparsePermutation.extend_completionEquiv {size : Nat}
    (state : SparsePermutation size) (room : state.used < size)
    (inputPosition outputPosition : Fin size)
    (freshInput : state.used ≤ inputPosition.val)
    (freshOutput : state.used ≤ outputPosition.val) :
    (state.extend room inputPosition outputPosition).Completion ≃
      {π : state.Completion // π.val (state.input inputPosition) = state.output outputPosition} where
  toFun π :=
    let facts := (state.extend_completion_iff room inputPosition outputPosition
      freshInput freshOutput π.val).mp π.property
    ⟨⟨π.val, facts.1⟩, facts.2⟩
  invFun π := ⟨π.val.val,
    (state.extend_completion_iff room inputPosition outputPosition
      freshInput freshOutput π.val.val).mpr ⟨π.val.property, π.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reversing the sparse state exchanges forward and inverse queries. -/
def SparsePermutation.reverse {size : Nat} (state : SparsePermutation size) :
    SparsePermutation size where
  used := state.used
  within := state.within
  inputs := state.outputs
  outputs := state.inputs
  inputLength := state.outputLength
  outputLength := state.inputLength

@[simp] theorem SparsePermutation.reverse_reverse {size : Nat}
    (state : SparsePermutation size) : state.reverse.reverse = state := rfl

/-- Reversing a completion inverts the eager permutation. -/
def SparsePermutation.reverse_completionEquiv {size : Nat}
    (state : SparsePermutation size) : state.reverse.Completion ≃ state.Completion where
  toFun π := ⟨π.val.symm, by
    rw [state.completion_iff]
    intro position member
    have eq := (state.reverse.completion_iff π.val).mp π.property position member
    exact π.val.symm_apply_eq.mpr eq.symm⟩
  invFun π := ⟨π.val.symm, by
    rw [state.reverse.completion_iff]
    intro position member
    have eq := (state.completion_iff π.val).mp π.property position member
    exact π.val.symm_apply_eq.mpr eq.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl


/-- An inverse query is a forward query in the reversed sparse state. -/
theorem SparsePermutation.inverse_reverse_forward {size : Nat}
    (state : SparsePermutation size) (y : Fin size) :
    state.inverse y = (state.reverse.forward y).map
      (fun pair => (pair.1, pair.2.reverse)) := by
  unfold inverse forward
  dsimp only [reverse, input, output]
  split <;> simp_all [Draw.map, extend, suffix]; rfl


/-- The programmed oracle keeps a sparse base and deferred output swaps. -/
structure ProgrammedPermutation (size : Nat) where
  base : SparsePermutation size
  overlay : List (Fin size × Fin size)

/-- The sparse initial oracle has no programmed swaps. -/
def ProgrammedPermutation.empty (size : Nat) : ProgrammedPermutation size :=
  ⟨SparsePermutation.empty size, []⟩

/-- This interpretation applies the deferred swaps to one eager completion. -/
def ProgrammedPermutation.denote {size : Nat} (state : ProgrammedPermutation size)
    (π : Equiv.Perm (Fin size)) : Equiv.Perm (Fin size) :=
  π.trans (swaps state.overlay)

/-- A forward query applies the deferred swaps after the base answer. -/
def ProgrammedPermutation.forward {size : Nat} (state : ProgrammedPermutation size)
    (input : Fin size) : Draw (Fin size × ProgrammedPermutation size) :=
  (state.base.forward input).map fun pair =>
    (swaps state.overlay pair.1, { state with base := pair.2 })

/-- An inverse query removes the deferred swaps before the base query. -/
def ProgrammedPermutation.inverse {size : Nat} (state : ProgrammedPermutation size)
    (output : Fin size) : Draw (Fin size × ProgrammedPermutation size) :=
  (state.base.inverse ((swaps state.overlay).symm output)).map fun pair =>
    (pair.1, { state with base := pair.2 })

/-- One programming step retains the sampled base pair and adds its output swap. -/
def ProgrammedPermutation.afterProgram {size : Nat} (state : ProgrammedPermutation size)
    (target answer : Fin size) (nextBase : SparsePermutation size) :
    ProgrammedPermutation size :=
  ⟨nextBase, programOverlay state.overlay (swaps state.overlay answer) target⟩

/-- Programming reads one sparse base answer and stores one deferred swap. -/
def ProgrammedPermutation.program {size : Nat} (state : ProgrammedPermutation size)
    (input target : Fin size) : Draw (ProgrammedPermutation size) :=
  (state.base.forward input).map fun pair => state.afterProgram target pair.1 pair.2

/-- The executable programming update gives the eager programmed permutation. -/
theorem ProgrammedPermutation.afterProgram_exact {size : Nat}
    (state : ProgrammedPermutation size) (input target : Fin size)
    (π : Equiv.Perm (Fin size)) (nextBase : SparsePermutation size) :
    (state.afterProgram target (π input) nextBase).denote π =
      (state.denote π).trans (Equiv.swap (state.denote π input) target) :=
  programOverlay_exact π state.overlay input target

/-- A programming update adds one overlay entry. -/
theorem ProgrammedPermutation.afterProgram_length {size : Nat}
    (state : ProgrammedPermutation size) (target answer : Fin size)
    (nextBase : SparsePermutation size) :
    (state.afterProgram target answer nextBase).overlay.length = state.overlay.length + 1 := by
  exact programOverlay_length state.overlay (swaps state.overlay answer) target

/-- A reached forward query adds at most one base pair. -/
theorem SparsePermutation.forward_used_le {size : Nat} (state : SparsePermutation size)
    (input : Fin size) (answer : Fin size × SparsePermutation size)
    (reached : answer ∈ (state.forward input).distribution.support) :
    answer.2.used ≤ state.used + 1 := by
  unfold forward at reached
  dsimp only at reached
  split at reached
  · simp only [Draw.distribution, PMF.mem_support_pure_iff] at reached
    rw [reached]
    exact Nat.le_succ _
  · obtain ⟨rank, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
    rw [← same]
    exact Nat.le_refl _

/-- A reached inverse query adds at most one base pair. -/
theorem SparsePermutation.inverse_used_le {size : Nat} (state : SparsePermutation size)
    (output : Fin size) (answer : Fin size × SparsePermutation size)
    (reached : answer ∈ (state.inverse output).distribution.support) :
    answer.2.used ≤ state.used + 1 := by
  unfold inverse at reached
  dsimp only at reached
  split at reached
  · simp only [Draw.distribution, PMF.mem_support_pure_iff] at reached
    rw [reached]
    exact Nat.le_succ _
  · obtain ⟨rank, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
    rw [← same]
    exact Nat.le_refl _

/-- A reached forward query preserves the overlay and adds at most one base pair. -/
theorem ProgrammedPermutation.forward_resources {size : Nat}
    (state : ProgrammedPermutation size) (input : Fin size)
    (answer : Fin size × ProgrammedPermutation size)
    (reached : answer ∈ (state.forward input).distribution.support) :
    answer.2.base.used ≤ state.base.used + 1 ∧ answer.2.overlay = state.overlay := by
  rw [forward, Draw.map_distribution] at reached
  obtain ⟨baseAnswer, baseReached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  rw [← same]
  exact ⟨state.base.forward_used_le input baseAnswer baseReached, rfl⟩

/-- A reached inverse query preserves the overlay and adds at most one base pair. -/
theorem ProgrammedPermutation.inverse_resources {size : Nat}
    (state : ProgrammedPermutation size) (output : Fin size)
    (answer : Fin size × ProgrammedPermutation size)
    (reached : answer ∈ (state.inverse output).distribution.support) :
    answer.2.base.used ≤ state.base.used + 1 ∧ answer.2.overlay = state.overlay := by
  rw [inverse, Draw.map_distribution] at reached
  obtain ⟨baseAnswer, baseReached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  rw [← same]
  exact ⟨state.base.inverse_used_le _ baseAnswer baseReached, rfl⟩

/-- A reached programming step adds one overlay entry and at most one base pair. -/
theorem ProgrammedPermutation.program_resources {size : Nat}
    (state : ProgrammedPermutation size) (input target : Fin size)
    (next : ProgrammedPermutation size)
    (reached : next ∈ (state.program input target).distribution.support) :
    next.base.used ≤ state.base.used + 1 ∧ next.overlay.length = state.overlay.length + 1 := by
  rw [program, Draw.map_distribution] at reached
  obtain ⟨baseAnswer, baseReached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  rw [← same]
  exact ⟨state.base.forward_used_le input baseAnswer baseReached,
    state.afterProgram_length target baseAnswer.1 baseAnswer.2⟩

/-- The bound counts the base and overlay equality tests for one query. -/
def ProgrammedPermutation.queryComparisons {size : Nat} (state : ProgrammedPermutation size) : Nat :=
  state.base.lookupComparisons + 2 * state.overlay.length

/-- The comparison bound depends only on the stored query and programming history. -/
theorem ProgrammedPermutation.queryComparisons_le {size : Nat}
    (state : ProgrammedPermutation size) :
    state.queryComparisons ≤ 4 * state.base.used + 2 * state.overlay.length := by
  exact Nat.add_le_add_right state.base.lookupComparisons_le _

/-- The hash table stores only the inputs that a run reaches. -/
abbrev HashTable (Key : Type) (size : Nat) := List (Key × Fin size)

/-- A hash query reuses an answer or draws one new bounded integer. -/
def HashTable.query {Key : Type} [DecidableEq Key] {size : Nat}
    (positive : 0 < size) (table : HashTable Key size) (key : Key) :
    Draw (Fin size × HashTable Key size) :=
  match table.lookup key with
  | some value => .pure (value, table)
  | none => .uniform size positive fun value => (value, (key, value) :: table)

/-- A hash update has the same lookup rule as an eager function update. -/
def HashTable.program {Key : Type} (table : HashTable Key size)
    (key : Key) (value : Fin size) : HashTable Key size := (key, value) :: table

theorem HashTable.program_lookup {Key : Type} [DecidableEq Key]
    (table : HashTable Key size) (key query : Key) (value : Fin size) :
    (table.program key value).lookup query =
      Function.update (fun k => table.lookup k) key (some value) query := by
  by_cases same : key = query
  · subst query; simp [program, List.lookup]
  · have different : (query == key) = false := by simp [Ne.symm same]
    simp [program, List.lookup, different, Ne.symm same]

/-- A reached hash query adds at most one table entry. -/
theorem HashTable.query_length_le {Key : Type} [DecidableEq Key] {size : Nat}
    (positive : 0 < size) (table : HashTable Key size) (key : Key)
    (answer : Fin size × HashTable Key size)
    (reached : answer ∈ (table.query positive key).distribution.support) :
    answer.2.length ≤ table.length + 1 := by
  unfold query at reached
  split at reached
  · simp only [Draw.distribution, PMF.mem_support_pure_iff] at reached
    rw [reached]
    exact Nat.le_succ _
  · obtain ⟨value, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
    rw [← same]
    exact Nat.le_refl _

/-- This type contains the eager functions consistent with the hash table. -/
abbrev HashTable.Completion {Key : Type} [DecidableEq Key]
    (table : HashTable Key size) :=
  {f : Key → Fin size // ∀ key value, table.lookup key = some value → f key = value}

noncomputable instance {Key : Type} [Fintype Key] [DecidableEq Key]
    (table : HashTable Key size) : Fintype table.Completion := by
  classical
  unfold HashTable.Completion
  infer_instance

instance {Key : Type} [DecidableEq Key] [Nonempty (Fin size)]
    (table : HashTable Key size) : Nonempty table.Completion := by
  classical
  refine ⟨⟨fun key => (table.lookup key).getD (Classical.choice inferInstance), ?_⟩⟩
  intro key value present
  simp [present]

/-- A fresh hash input permits every new value. -/
def HashTable.updateCompletion {Key : Type} [DecidableEq Key]
    (table : HashTable Key size) (key : Key) (fresh : table.lookup key = none)
    (f : table.Completion) (value : Fin size) : table.Completion :=
  ⟨Function.update f.val key value, by
    intro query answer present
    have different : query ≠ key := by
      intro same
      subst query
      simp [fresh] at present
    rw [Function.update_of_ne different]
    exact f.property query answer present⟩

/-- One fresh value and its remaining completion form a product. -/
def HashTable.freshCompletionEquiv {Key : Type} [DecidableEq Key]
    (table : HashTable Key size) (key : Key) (fresh : table.lookup key = none)
    (zero : Fin size) :
    table.Completion ≃ Fin size × {f : table.Completion // f.val key = zero} where
  toFun f := (f.val key, ⟨table.updateCompletion key fresh f zero, by
    simp [updateCompletion]⟩)
  invFun pair := table.updateCompletion key fresh pair.2.val pair.1
  left_inv f := by
    apply Subtype.ext
    funext query
    by_cases same : query = key
    · subst query; simp [updateCompletion]
    · simp [updateCompletion]
  right_inv pair := by
    apply Prod.ext
    · simp [updateCompletion]
    · apply Subtype.ext
      apply Subtype.ext
      funext query
      by_cases same : query = key
      · subst query; simp [updateCompletion, pair.2.property]
      · simp [updateCompletion, Function.update_of_ne same]


/-- A fresh table entry adds exactly one equation to the eager fiber. -/
theorem HashTable.extend_completion_iff {Key : Type} [DecidableEq Key]
    (table : HashTable Key size) (key : Key) (fresh : table.lookup key = none)
    (value : Fin size) (f : Key → Fin size) :
    (∀ query answer, (table.program key value).lookup query = some answer → f query = answer) ↔
      (∀ query answer, table.lookup query = some answer → f query = answer) ∧ f key = value := by
  constructor
  · intro compatible
    constructor
    · intro query answer present
      apply compatible query answer
      rw [program_lookup, Function.update_of_ne]
      · exact present
      · intro same; subst query; simp [fresh] at present
    · apply compatible key value
      simp [program_lookup]
  · rintro ⟨compatible, valueEq⟩ query answer present
    rw [program_lookup] at present
    by_cases same : query = key
    · subst query
      simp only [Function.update_self, Option.some.injEq] at present
      exact valueEq.trans present
    · rw [Function.update_of_ne same] at present
      exact compatible query answer present

/-- The fresh hash update preserves its full conditional eager fiber. -/
def HashTable.extend_completionEquiv {Key : Type} [DecidableEq Key]
    (table : HashTable Key size) (key : Key) (fresh : table.lookup key = none)
    (value : Fin size) :
    (table.program key value).Completion ≃ {f : table.Completion // f.val key = value} where
  toFun f :=
    let facts := (table.extend_completion_iff key fresh value f.val).mp f.property
    ⟨⟨f.val, facts.1⟩, facts.2⟩
  invFun f := ⟨f.val.val,
    (table.extend_completion_iff key fresh value f.val.val).mpr ⟨f.val.property, f.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Kriterion.ArgoMAC.Security.OperationalOracle
