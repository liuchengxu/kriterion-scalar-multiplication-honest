import Proof.Privacy.Simulator.OperationalProgramLaw
import Mathlib.Data.Fin.Tuple.Basic

namespace Kriterion.ArgoMAC.Security.OperationalOracle
open Cryptography
/-- The executable family operation samples only the selected sparse oracle. -/
def familyDraw {Index : Type} [DecidableEq Index] {size : Nat}
    (query : Index × ProgramAction size) (state : Index → ProgrammedPermutation size) :
    Draw (Fin size × (Index → ProgrammedPermutation size)) :=
  let selected := state query.1
  let draw := match query.2 with
    | .forward input => selected.forward input
    | .inverse output => selected.inverse output
    | .program input target => (selected.program input target).map (fun next => (target, next))
  draw.map (fun answer => (answer.1, Function.update state query.1 answer.2))

noncomputable section

/-- The family kernel samples independent conditional completions at all indices. -/
def finiteKernel {Sparse Eager : Type} (kernel : Sparse → PMF Eager) :
    {count : Nat} → (Fin count → Sparse) → PMF (Fin count → Eager)
  | 0, _ => PMF.pure Fin.elim0
  | _ + 1, state =>
      (kernel (state 0)).bind (fun head =>
        (finiteKernel kernel (Fin.tail state)).map (Fin.cons head))

/-- A family request selects one local oracle. -/
abbrev indexedSpec (Index : Type) (oracle : OracleSpec) : OracleSpec where
  Query := Index × oracle.Query
  Answer query := oracle.Answer query.2

/-- The eager family interpreter updates only the selected local state. -/
def indexedEager {Index State : Type} [DecidableEq Index] {oracle : OracleSpec}
    (handler : OracleHandler oracle State) : OracleHandler (indexedSpec Index oracle) (Index → State) :=
  fun query state =>
    let answer := handler query.2 (state query.1)
    (answer.1, Function.update state query.1 answer.2)

/-- The sampled family interpreter also updates only the selected local state. -/
def indexedSampled {Index State : Type} [DecidableEq Index] {oracle : OracleSpec}
    (handler : ∀ query, State → PMF (oracle.Answer query × State)) :
    ∀ query : (indexedSpec Index oracle).Query,
      (Index → State) → PMF ((indexedSpec Index oracle).Answer query × (Index → State)) :=
  fun query state => (handler query.2 (state query.1)).map
    (fun answer => (answer.1, Function.update state query.1 answer.2))

/-- Independent completion kernels preserve the local joint law at every family index. -/
theorem finiteKernel_step {oracle : OracleSpec} {Sparse Eager : Type}
    (eager : OracleHandler oracle Eager)
    (sampled : ∀ query, Sparse → PMF (oracle.Answer query × Sparse))
    (kernel : Sparse → PMF Eager)
    (step : ∀ query state,
      (kernel state).map (eager query) =
        (sampled query state).bind (fun answer =>
          (kernel answer.2).map (fun eagerState => (answer.1, eagerState))))
    {count : Nat} (query : (indexedSpec (Fin count) oracle).Query) (state : Fin count → Sparse) :
    (finiteKernel kernel state).map (indexedEager eager query) =
      (indexedSampled sampled query state).bind (fun answer =>
        (finiteKernel kernel answer.2).map (fun eagerState => (answer.1, eagerState))) := by
  induction count with
  | zero => exact Fin.elim0 query.1
  | succ count inductionHypothesis =>
      rcases query with ⟨index, request⟩
      refine Fin.cases ?_ (fun index => ?_) index
      · simp only [finiteKernel, indexedEager, indexedSampled, PMF.map_bind, PMF.map_comp,
          PMF.bind_map, Function.comp_def, Fin.cons_zero, Function.update_self, Fin.tail_update_zero]
        have law := congrArg
          (fun distribution : PMF (oracle.Answer request × Eager) =>
            distribution.bind (fun answer => (finiteKernel kernel (Fin.tail state)).map
              (fun tail => (answer.1, (Fin.cons answer.2 tail : Fin (count + 1) → Eager))))) (step request (state 0))
        simp only [PMF.bind_map, PMF.bind_bind, Function.comp_def] at law
        simpa only [Fin.update_cons_zero] using law
      · simp only [finiteKernel, indexedEager, indexedSampled, PMF.map_bind, PMF.map_comp,
          PMF.bind_map, Function.comp_def, Fin.cons_succ, Function.update_of_ne (Ne.symm (Fin.succ_ne_zero index)),
          Fin.tail_update_succ]
        have law := inductionHypothesis (query := (index, request)) (state := Fin.tail state)
        simp only [indexedSampled, PMF.bind_map, Function.comp_def] at law
        have mapped := congrArg
          (fun distribution : PMF (oracle.Answer request × (Fin count → Eager)) =>
            (kernel (state 0)).bind (fun head => distribution.map
              (fun answer => (answer.1, (Fin.cons head answer.2 : Fin (count + 1) → Eager))))) law
        simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at mapped
        simp_rw [← Fin.cons_update]
        apply mapped.trans
        exact PMF.bind_comm _ _ _

/-- This equality transports a local update through a finite index equivalence. -/
theorem update_reindex {Index Other Value : Type} [DecidableEq Index] [DecidableEq Other]
    (equiv : Other ≃ Index) (function : Index → Value) (index : Index) (value : Value) :
    (fun other => Function.update function index value (equiv other)) =
      Function.update (fun other => function (equiv other)) (equiv.symm index) value :=
  Function.update_comp_equiv function equiv index value

/-- The finite kernel uses the supplied index type without changing its queries. -/
def indexedKernel {Index Sparse Eager : Type} [Fintype Index]
    (kernel : Sparse → PMF Eager) (state : Index → Sparse) : PMF (Index → Eager) :=
  (finiteKernel kernel (fun index => state ((Fintype.equivFin Index).symm index))).map
    (fun complete index => complete (Fintype.equivFin Index index))

/-- The family coupling holds for every finite index type. -/
theorem indexedKernel_step {Index : Type} [Fintype Index] [DecidableEq Index]
    {oracle : OracleSpec} {Sparse Eager : Type}
    (eager : OracleHandler oracle Eager)
    (sampled : ∀ query, Sparse → PMF (oracle.Answer query × Sparse))
    (kernel : Sparse → PMF Eager)
    (step : ∀ query state,
      (kernel state).map (eager query) =
        (sampled query state).bind (fun answer =>
          (kernel answer.2).map (fun eagerState => (answer.1, eagerState))))
    (query : (indexedSpec Index oracle).Query) (state : Index → Sparse) :
    (indexedKernel kernel state).map (indexedEager eager query) =
      (indexedSampled sampled query state).bind (fun answer =>
        (indexedKernel kernel answer.2).map (fun eagerState => (answer.1, eagerState))) := by
  rcases query with ⟨index, request⟩
  let equiv := Fintype.equivFin Index
  have law := finiteKernel_step eager sampled kernel step (equiv index, request)
    (fun position => state (equiv.symm position))
  have mapped := congrArg
    (fun distribution : PMF (oracle.Answer request × (Fin (Fintype.card Index) → Eager)) =>
      distribution.map (fun result => (result.1, fun index => result.2 (equiv index)))) law
  simp only [indexedEager, indexedSampled, PMF.map_bind, PMF.map_comp, PMF.bind_map,
    Function.comp_def, Equiv.symm_apply_apply] at mapped
  simp_rw [update_reindex equiv, Equiv.symm_apply_apply] at mapped
  simp only [indexedKernel, indexedEager, indexedSampled, PMF.map_comp,
    PMF.bind_map, Function.comp_def]
  simp_rw [update_reindex (Fintype.equivFin Index).symm, Equiv.symm_symm]
  exact mapped

/-- A family state stores only the sparse oracle data at each finite index. -/
abbrev FamilyState (Index : Type) (size : Nat) := Index → ProgrammedPermutation size

/-- The family accepts forward, inverse, and programming requests at every index. -/
abbrev familySpec (Index : Type) (size : Nat) := indexedSpec Index (programSpec size)

/-- The family interpreter samples only the selected sparse oracle. -/
def familySampled {Index : Type} [DecidableEq Index] {size : Nat} :=
  indexedSampled (Index := Index) (programSampled (size := size))

/-- The executable family draw has the sampled handler's exact distribution. -/
theorem familyDraw_distribution {Index : Type} [DecidableEq Index] {size : Nat}
    (query : Index × ProgramAction size) (state : FamilyState Index size) :
    (familyDraw query state).distribution = familySampled query state := by
  rcases query with ⟨index, action⟩
  cases action <;> simp only [familyDraw, familySampled, indexedSampled, programSampled,
    Draw.map_distribution, PMF.map_comp]

/-- The eager interpreter keeps each base permutation and its deferred swaps. -/
def familyEager {Index : Type} [DecidableEq Index] {size : Nat} :=
  indexedEager (Index := Index) (programEager (size := size))

/-- The completed family retains the independent conditional law at all indices. -/
def familyCompletion {Index : Type} [Fintype Index] {size : Nat} :=
  indexedKernel (Index := Index) (programCompletion (size := size))

/-- The concrete indexed family satisfies the complete one-step joint law. -/
theorem family_step {Index : Type} [Fintype Index] [DecidableEq Index] {size : Nat}
    (query : (familySpec Index size).Query) (state : FamilyState Index size) :
    (familyCompletion state).map (familyEager query) =
      (familySampled query state).bind (fun answer =>
        (familyCompletion answer.2).map (fun eagerState => (answer.1, eagerState))) :=
  indexedKernel_step programEager programSampled programCompletion program_step query state


/-- Mapping each local completion commutes with the independent family kernel. -/
theorem finiteKernel_map {Sparse Eager View : Type} (kernel : Sparse → PMF Eager)
    (view : Eager → View) {count : Nat} (state : Fin count → Sparse) :
    (finiteKernel kernel state).map (fun complete => view ∘ complete) =
      finiteKernel (fun state => (kernel state).map view) state := by
  induction count with
  | zero =>
      simp only [finiteKernel, PMF.pure_map]
      congr 1
      funext index
      exact Fin.elim0 index
  | succ count inductionHypothesis =>
      simp only [finiteKernel, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]
      congr 1
      funext head
      have law := congrArg
        (fun distribution : PMF (Fin count → View) => distribution.map (fun tail => (Fin.cons (view head) tail : Fin (count + 1) → View)))
        (inductionHypothesis (state := Fin.tail state))
      have composed (tail : Fin count → Eager) :
          (fun index : Fin (count + 1) => view ((Fin.cons head tail : Fin (count + 1) → Eager) index)) =
            Fin.cons (view head) (fun index => view (tail index)) := by
        funext index
        exact Fin.cases rfl (fun _ => rfl) index
      calc
        _ = (finiteKernel kernel (Fin.tail state)).map
            (fun tail => (Fin.cons (view head) (fun index => view (tail index)) : Fin (count + 1) → View)) := by
          congr 1
          funext tail
          exact composed tail
        _ = _ := by simpa only [PMF.map_comp, Function.comp_def] using law

/-- Independent uniform local samples give the exact uniform finite function. -/
theorem finiteKernel_uniform (Value : Type) [Fintype Value] [Nonempty Value] (count : Nat) :
    finiteKernel (fun _ : Unit => PMF.uniformOfFintype Value) (fun _ : Fin count => ()) =
      PMF.uniformOfFintype (Fin count → Value) := by
  induction count with
  | zero =>
      have equal (function : Fin 0 → Value) : function = Fin.elim0 := by
        funext index
        exact Fin.elim0 index
      ext function
      simp [finiteKernel, PMF.pure_apply, equal function, PMF.uniformOfFintype_apply]
  | succ count inductionHypothesis =>
      change (PMF.uniformOfFintype Value).bind (fun head =>
        (finiteKernel (fun _ : Unit => PMF.uniformOfFintype Value) (fun _ : Fin count => ())).map
          (fun tail => (Fin.cons head tail : Fin (count + 1) → Value))) = _
      rw [inductionHypothesis]
      have law := congrArg
        (fun distribution : PMF (Value × (Fin count → Value)) => distribution.map
          (Fin.consEquiv (fun _ : Fin (count + 1) => Value)))
        (uniform_product (A := Value) (B := Fin count → Value))
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at law
      exact law.trans (uniform_equiv (Fin.consEquiv (fun _ : Fin (count + 1) => Value)))

/-- Equal local kernels give equal independent families. -/
theorem finiteKernel_congr {First Second Eager : Type}
    (first : First → PMF Eager) (second : Second → PMF Eager)
    {count : Nat} (left : Fin count → First) (right : Fin count → Second)
    (equal : ∀ index, first (left index) = second (right index)) :
    finiteKernel first left = finiteKernel second right := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [finiteKernel, equal 0]
      congr 1
      funext head
      congr 1
      exact inductionHypothesis (Fin.tail left) (Fin.tail right) (fun index => equal index.succ)

/-- The empty programmed oracle denotes the exact full uniform permutation. -/
theorem program_initial_denote (size : Nat) :
    (programCompletion (ProgrammedPermutation.empty size)).map
        (fun complete => complete.1.denote complete.2) =
      PMF.uniformOfFintype (Equiv.Perm (Fin size)) := by
  simp only [programCompletion, ProgrammedPermutation.empty, ProgrammedPermutation.denote,
    swaps_nil, PMF.map_comp, Function.comp_def]
  convert uniform_equiv (emptyCompletionEquiv size) using 1; rfl

/-- The complete empty family denotes the exact independent uniform permutation family. -/
theorem family_initial_denote {Index : Type} [Fintype Index] [DecidableEq Index] (size : Nat) :
    (familyCompletion (fun _ : Index => ProgrammedPermutation.empty size)).map
        (fun complete index => (complete index).1.denote (complete index).2) =
      PMF.uniformOfFintype (Index → Equiv.Perm (Fin size)) := by
  classical
  let view := fun complete : ProgrammedPermutation size × Equiv.Perm (Fin size) =>
    complete.1.denote complete.2
  have finite := finiteKernel_map programCompletion view
    (fun _ : Fin (Fintype.card Index) => ProgrammedPermutation.empty size)
  have replaced := finiteKernel_congr
    (fun state => (programCompletion state).map view)
    (fun _ : Unit => PMF.uniformOfFintype (Equiv.Perm (Fin size)))
    (fun _ : Fin (Fintype.card Index) => ProgrammedPermutation.empty size)
    (fun _ : Fin (Fintype.card Index) => ())
    (fun _ => program_initial_denote size)
  have exactFinite := finite.trans (replaced.trans (finiteKernel_uniform _ _))
  let equiv : (Fin (Fintype.card Index) → Equiv.Perm (Fin size)) ≃
      (Index → Equiv.Perm (Fin size)) := {
    toFun := fun complete index => complete (Fintype.equivFin Index index)
    invFun := fun complete index => complete ((Fintype.equivFin Index).symm index)
    left_inv := by intro complete; funext index; simp
    right_inv := by intro complete; funext index; simp
  }
  have mapped := congrArg (fun distribution : PMF (Fin (Fintype.card Index) → Equiv.Perm (Fin size)) =>
    distribution.map equiv) exactFinite
  simp only [PMF.map_comp, Function.comp_def] at mapped
  simp only [familyCompletion, indexedKernel, PMF.map_comp, Function.comp_def]
  convert mapped.trans (uniform_equiv equiv) using 1; rfl

end
end Kriterion.ArgoMAC.Security.OperationalOracle
