import Proof.Privacy.Simulator.OperationalOracle
import Cryptography.Primitives

namespace Kriterion.ArgoMAC.Security.OperationalOracle
open Cryptography
noncomputable section

/-- A product of uniform finite samples is uniform. -/
theorem uniform_product {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    (PMF.uniformOfFintype A).bind (fun a => (PMF.uniformOfFintype B).map (fun b => (a, b))) =
      PMF.uniformOfFintype (A × B) := by
  classical
  letI : DecidableEq A := Classical.decEq A
  letI : DecidableEq B := Classical.decEq B
  apply PMF.ext
  rintro ⟨a, b⟩
  simp only [PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply, Prod.mk.injEq,
    ite_and, Fintype.card_prod, Nat.cast_mul]
  have inner (a' : A) :
      (∑' b' : B, if a = a' then if b = b' then (Fintype.card B : ENNReal)⁻¹ else 0 else 0) =
        if a = a' then (Fintype.card B : ENNReal)⁻¹ else 0 := by
    by_cases equal : a = a'
    · simp only [if_pos equal]
      simp_rw [@eq_comm B b]
      exact tsum_ite_eq _ _
    · simp only [if_neg equal, tsum_zero]
  simp_rw [inner]
  simp_rw [mul_ite, mul_zero, @eq_comm A a]
  rw [tsum_ite_eq]
  exact (ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _))).symm

/-- A finite bijection preserves the uniform law. -/
theorem uniform_equiv {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (equiv : A ≃ B) : (PMF.uniformOfFintype A).map equiv = PMF.uniformOfFintype B :=
  PMF.uniformOfFintype_map_of_bijective equiv equiv.bijective

/-- A product representation identifies each conditional fiber exactly. -/
def productFiberEquiv {A B C : Type} (equiv : A ≃ B × C) (value : B) :
    C ≃ {a : A // (equiv a).1 = value} where
  toFun c := ⟨equiv.symm (value, c), by simp⟩
  invFun a := (equiv a.val).2
  left_inv c := by simp
  right_inv a := by
    apply Subtype.ext
    apply equiv.injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext a.property.symm rfl

/-- A uniform sample splits into a uniform answer and its full conditional fiber. -/
theorem uniform_fiber {A B C : Type} [Fintype A] [Fintype B] [Fintype C] [DecidableEq B]
    [Nonempty A] [Nonempty B] [Nonempty C] (equiv : A ≃ B × C) :
    PMF.uniformOfFintype A =
      (PMF.uniformOfFintype B).bind (fun b =>
        letI : Nonempty {a : A // (equiv a).1 = b} := ⟨productFiberEquiv equiv b (Classical.choice inferInstance)⟩
        (PMF.uniformOfFintype {a : A // (equiv a).1 = b}).map Subtype.val) := by
  classical
  have fiber (b : B) :
      letI : Nonempty {a : A // (equiv a).1 = b} := ⟨productFiberEquiv equiv b (Classical.choice inferInstance)⟩
      (PMF.uniformOfFintype {a : A // (equiv a).1 = b}).map Subtype.val =
        (PMF.uniformOfFintype C).map (fun c => equiv.symm (b, c)) := by
    letI : Nonempty {a : A // (equiv a).1 = b} := ⟨productFiberEquiv equiv b (Classical.choice inferInstance)⟩
    rw [← uniform_equiv (productFiberEquiv equiv b), PMF.map_comp]
    rfl
  simp_rw [fiber]
  have law := congrArg (fun distribution : PMF (B × C) => distribution.map equiv.symm)
    (uniform_product (A := B) (B := C))
  simp only [PMF.map_bind, PMF.map_comp] at law
  exact (law.trans (uniform_equiv equiv.symm)).symm

/-- This function records the pair that an eager forward query reveals. -/
def SparsePermutation.afterForward {size : Nat} (state : SparsePermutation size)
    (x y : Fin size) : SparsePermutation size :=
  if known : state.knownInput x then state
  else state.extend (by have := (state.input.symm x).isLt; unfold knownInput at known; omega)
    (state.input.symm x) (state.output.symm y)

theorem SparsePermutation.afterForward_of_fresh {size : Nat} (state : SparsePermutation size)
    (x : Fin size) (fresh : ¬ state.knownInput x) (y : Fin size)
    (room : state.used < size) :
    state.afterForward x y = state.extend room (state.input.symm x) (state.output.symm y) := by
  unfold afterForward
  split
  · contradiction
  · rfl

/-- A fresh output separates the eager completion into an answer and a fixed fiber. -/
def SparsePermutation.answerEquiv {size : Nat} (state : SparsePermutation size)
    (x : Fin size) (fresh : ¬ state.knownInput x)
    (reference : {y : Fin size // ¬ state.knownOutput y}) :
    state.Completion ≃ {y : Fin size // ¬ state.knownOutput y} ×
      {π : Equiv.Perm (Fin size) //
        (∀ a : {a : Fin size // state.knownInput a}, π a = state.assignment a) ∧
        π x = reference.val} :=
  (programCompatiblePermutationEquiv {a | state.knownInput a} {a | state.knownOutput a}
    state.assignment x fresh reference.val reference.property).trans (Equiv.prodComm _ _)

/-- The answer fiber is exactly the completed sparse update. -/
def SparsePermutation.answerFiberEquiv {size : Nat} (state : SparsePermutation size)
    (x : Fin size) (fresh : ¬ state.knownInput x)
    (reference answer : {y : Fin size // ¬ state.knownOutput y}) :
    (state.afterForward x answer.val).Completion ≃
      {π : state.Completion // (state.answerEquiv x fresh reference π).1 = answer} := by
  have room : state.used < size := by
    have := (state.input.symm x).isLt
    unfold knownInput at fresh
    omega
  have freshInput : state.used ≤ (state.input.symm x).val := Nat.le_of_not_gt fresh
  have freshOutput : state.used ≤ (state.output.symm answer.val).val :=
    Nat.le_of_not_gt answer.property
  have same (π : state.Completion) :
      π.val (state.input (state.input.symm x)) = state.output (state.output.symm answer.val) ↔
        (state.answerEquiv x fresh reference π).1 = answer := by
    simp only [Equiv.apply_symm_apply]
    constructor
    · intro equal
      apply Subtype.ext
      exact equal
    · intro equal
      exact congrArg Subtype.val equal
  have transport (π : Equiv.Perm (Fin size)) :
      (∀ a : {a : Fin size // (state.afterForward x answer.val).knownInput a},
        π a = (state.afterForward x answer.val).assignment a) ↔
      (∀ a : {a : Fin size // state.knownInput a}, π a = state.assignment a) ∧
        π (state.input (state.input.symm x)) = state.output (state.output.symm answer.val) := by
    rw [state.afterForward_of_fresh x fresh answer.val room]
    exact state.extend_completion_iff room (state.input.symm x)
      (state.output.symm answer.val) freshInput freshOutput π
  exact {
    toFun := fun π =>
      ⟨⟨π.val, ((transport π.val).mp π.property).1⟩,
        (same _).mp ((transport π.val).mp π.property).2⟩
    invFun := fun π =>
      ⟨π.val.val, (transport π.val.val).mpr ⟨π.val.property, (same π.val).mpr π.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }

/-- A sparse update retains the exact full conditional permutation law. -/
theorem SparsePermutation.forward_fresh_completion {size : Nat}
    (state : SparsePermutation size) (x : Fin size) (fresh : ¬ state.knownInput x)
    (reference : {y : Fin size // ¬ state.knownOutput y}) :
    letI : Nonempty {y : Fin size // ¬ state.knownOutput y} := ⟨reference⟩
    (PMF.uniformOfFintype state.Completion).map Subtype.val =
      (PMF.uniformOfFintype {y : Fin size // ¬ state.knownOutput y}).bind (fun answer =>
        (PMF.uniformOfFintype (state.afterForward x answer.val).Completion).map Subtype.val) := by
  classical
  letI : Nonempty {y : Fin size // ¬ state.knownOutput y} := ⟨reference⟩
  let equiv := state.answerEquiv x fresh reference
  letI : Nonempty {π : Equiv.Perm (Fin size) //
      (∀ a : {a : Fin size // state.knownInput a}, π a = state.assignment a) ∧
      π x = reference.val} :=
    ⟨(equiv (Classical.choice inferInstance)).2⟩
  have split := congrArg (fun distribution : PMF state.Completion => distribution.map Subtype.val)
    (uniform_fiber equiv)
  simp only [PMF.map_bind, PMF.map_comp] at split
  rw [split]
  congr 1
  funext answer
  letI : Nonempty {π : state.Completion // (equiv π).1 = answer} :=
    ⟨state.answerFiberEquiv x fresh reference answer (Classical.choice inferInstance)⟩
  rw [← uniform_equiv (state.answerFiberEquiv x fresh reference answer), PMF.map_comp]
  rfl

/-- A completed fresh update contains its newly revealed pair. -/
theorem SparsePermutation.afterForward_pair {size : Nat}
    (state : SparsePermutation size) (x : Fin size) (fresh : ¬ state.knownInput x)
    (answer : {y : Fin size // ¬ state.knownOutput y})
    (π : (state.afterForward x answer.val).Completion) : π.val x = answer.val :=
  congrArg Subtype.val (state.answerFiberEquiv x fresh answer answer π).property

/-- The forward law preserves the answer, sparse state, and complete eager permutation together. -/
theorem SparsePermutation.forward_joint {size : Nat}
    (state : SparsePermutation size) (x : Fin size) :
    (PMF.uniformOfFintype state.Completion).map
        (fun π => (π.val x, state.afterForward x (π.val x), π.val)) =
      (state.forward x).distribution.bind (fun answer =>
        (PMF.uniformOfFintype answer.2.Completion).map
          (fun π => (answer.1, answer.2, π.val))) := by
  classical
  by_cases known : state.knownInput x
  · have same (π : state.Completion) : π.val x = state.output (state.input.symm x) :=
      π.property ⟨x, known⟩
    simp only [forward, knownInput] at known ⊢
    simp only [dif_pos known, Draw.distribution, PMF.pure_bind]
    simp_rw [same]
    simp [afterForward, knownInput, known]
  · have room : state.used < size := by
      have := (state.input.symm x).isLt
      unfold knownInput at known
      omega
    letI : Nonempty (Fin (size - state.used)) := ⟨⟨0, by omega⟩⟩
    let reference := state.unusedOutputEquiv ⟨0, by omega⟩
    letI : Nonempty {y : Fin size // ¬ state.knownOutput y} := ⟨reference⟩
    have joint := congrArg
      (fun distribution : PMF (Equiv.Perm (Fin size)) => distribution.map
        (fun π => (π x, state.afterForward x (π x), π)))
      (state.forward_fresh_completion x known reference)
    simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at joint
    simp_rw [state.afterForward_pair x known] at joint
    apply joint.trans
    rw [← state.unusedOutput_uniform room, PMF.bind_map]
    simp only [forward, knownInput] at known ⊢
    simp only [dif_neg known, Draw.distribution, PMF.bind_map, Function.comp_def]
    congr 1
    funext rank
    change (PMF.uniformOfFintype
        (state.afterForward x (state.output (state.suffix rank))).Completion).map
        (fun π => (state.output (state.suffix rank),
          state.afterForward x (state.output (state.suffix rank)), π.val)) = _
    rw [state.afterForward_of_fresh x known (state.output (state.suffix rank)) room]
    rw [Equiv.symm_apply_apply]

/-- An inverse query records the same pair in the reversed sparse state. -/
def SparsePermutation.afterInverse {size : Nat} (state : SparsePermutation size)
    (y x : Fin size) : SparsePermutation size := (state.reverse.afterForward y x).reverse

/-- The inverse law preserves the answer, sparse state, and complete eager permutation together. -/
theorem SparsePermutation.inverse_joint {size : Nat}
    (state : SparsePermutation size) (y : Fin size) :
    (PMF.uniformOfFintype state.Completion).map
        (fun π => (π.val.symm y, state.afterInverse y (π.val.symm y), π.val)) =
      (state.inverse y).distribution.bind (fun answer =>
        (PMF.uniformOfFintype answer.2.Completion).map
          (fun π => (answer.1, answer.2, π.val))) := by
  have reversed := congrArg
    (fun distribution : PMF (Fin size × SparsePermutation size × Equiv.Perm (Fin size)) =>
      distribution.map (fun output => (output.1, output.2.1.reverse, output.2.2.symm)))
    (state.reverse.forward_joint y)
  simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at reversed
  have source := congrArg
    (fun distribution : PMF state.Completion => distribution.map
      (fun π => (π.val.symm y, state.afterInverse y (π.val.symm y), π.val)))
    (uniform_equiv state.reverse_completionEquiv)
  simp only [PMF.map_comp, Function.comp_def] at source
  calc
    _ = (PMF.uniformOfFintype state.reverse.Completion).map
        (fun π => (π.val y, (state.reverse.afterForward y (π.val y)).reverse, π.val.symm)) :=
      source.symm
    _ = _ := by
      apply reversed.trans
      rw [inverse_reverse_forward, Draw.map_distribution, PMF.bind_map]
      congr 1
      funext answer
      have target := congrArg
        (fun distribution : PMF answer.2.reverse.Completion => distribution.map
          (fun π => (answer.1, answer.2.reverse, π.val)))
        (uniform_equiv answer.2.reverse_completionEquiv.symm)
      simp only [PMF.map_comp, Function.comp_def] at target
      convert target using 1 <;> rfl

/-- This interpreter samples each oracle transition when a query reaches it. -/
def runSampled {oracle : OracleSpec} {Result State : Type}
    (handler : ∀ query, State → PMF (oracle.Answer query × State)) :
    {budget : Nat} → OracleProgram oracle Result budget → State → PMF (Result × State)
  | _, .pure distribution, state => distribution.map (fun value => (value, state))
  | _, .query request next, state =>
      (handler request state).bind (fun answer => runSampled handler (next answer.1) answer.2)
  | _, .sample distribution next, state =>
      distribution.bind (fun value => runSampled handler (next value) state)

/-- A one-step joint law extends to every adaptive oracle program. -/
theorem adaptive_joint_law {oracle : OracleSpec} {Result Sparse Eager : Type}
    (eager : OracleHandler oracle Eager)
    (sparse : ∀ query, Sparse → PMF (oracle.Answer query × Sparse))
    (completion : Sparse → PMF Eager)
    (step : ∀ query state,
      (completion state).map (eager query) =
        (sparse query state).bind (fun answer =>
          (completion answer.2).map (fun eagerState => (answer.1, eagerState))))
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : Sparse) :
    (completion state).bind (fun eagerState => program.run eager eagerState) =
      (runSampled sparse program state).bind (fun output =>
        (completion output.2).map (fun eagerState => (output.1, eagerState))) := by
  induction program generalizing state with
  | pure distribution =>
      simp only [OracleProgram.run_pure, runSampled, PMF.bind_map, Function.comp_def]
      exact PMF.bind_comm _ _ _
  | query request next inductionHypothesis =>
      simp only [OracleProgram.run_query, runSampled, PMF.bind_bind]
      have transformed := congrArg
        (fun distribution : PMF (oracle.Answer request × Eager) =>
          distribution.bind (fun answer => (next answer.1).run eager answer.2)) (step request state)
      simp only [PMF.bind_map, Function.comp_def, PMF.bind_bind] at transformed
      rw [transformed]
      simp_rw [inductionHypothesis]
  | sample distribution next inductionHypothesis =>
      simp only [OracleProgram.run_sample, runSampled, PMF.bind_bind]
      rw [PMF.bind_comm]
      simp_rw [inductionHypothesis]


/-- The empty sparse state permits every eager permutation. -/
def emptyCompletionEquiv (size : Nat) :
    (SparsePermutation.empty size).Completion ≃ Equiv.Perm (Fin size) where
  toFun := Subtype.val
  invFun π := ⟨π, by intro a; exact (Nat.not_lt_zero _ a.property).elim⟩
  left_inv _ := rfl
  right_inv _ := rfl


end
end Kriterion.ArgoMAC.Security.OperationalOracle
