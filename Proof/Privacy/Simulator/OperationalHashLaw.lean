import Proof.Privacy.Simulator.OperationalOracleLaw

namespace Kriterion.ArgoMAC.Security.OperationalOracle
open Cryptography
noncomputable section


/-- The hash state records a new answer only when the input is fresh. -/
def HashTable.afterQuery {Key : Type} [DecidableEq Key]
    (table : HashTable Key size) (key : Key) (value : Fin size) : HashTable Key size :=
  match table.lookup key with
  | none => table.program key value
  | some _ => table

/-- A fresh hash query preserves the entire conditional eager function. -/
theorem HashTable.fresh_completion {Key : Type} [Fintype Key] [DecidableEq Key]
    (positive : 0 < size) (table : HashTable Key size) (key : Key)
    (fresh : table.lookup key = none) :
    letI : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
    (PMF.uniformOfFintype table.Completion).map Subtype.val =
      (PMF.uniformOfFintype (Fin size)).bind (fun answer =>
        (PMF.uniformOfFintype (table.program key answer).Completion).map Subtype.val) := by
  classical
  letI : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
  let zero : Fin size := ⟨0, positive⟩
  let equiv := table.freshCompletionEquiv key fresh zero
  letI : Nonempty {f : table.Completion // f.val key = zero} :=
    ⟨⟨table.updateCompletion key fresh (Classical.choice inferInstance) zero, by
      simp [updateCompletion]⟩⟩
  have split := congrArg
    (fun distribution : PMF table.Completion => distribution.map Subtype.val)
    (uniform_fiber equiv)
  simp only [PMF.map_bind, PMF.map_comp] at split
  rw [split]
  congr 1
  funext answer
  letI : Nonempty {f : table.Completion // (equiv f).1 = answer} :=
    ⟨table.extend_completionEquiv key fresh answer (Classical.choice inferInstance)⟩
  letI : Nonempty {f : table.Completion // f.val key = answer} :=
    ⟨table.extend_completionEquiv key fresh answer (Classical.choice inferInstance)⟩
  change (PMF.uniformOfFintype {f : table.Completion // f.val key = answer}).map
    (fun f => f.val.val) = _
  rw [← uniform_equiv (table.extend_completionEquiv key fresh answer), PMF.map_comp]
  rfl

/-- The one-query law preserves the answer, hash table, and eager function together. -/
theorem HashTable.query_joint {Key : Type} [Fintype Key] [DecidableEq Key]
    (positive : 0 < size) (table : HashTable Key size) (key : Key) :
    letI : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
    (PMF.uniformOfFintype table.Completion).map
        (fun f => (f.val key, table.afterQuery key (f.val key), f.val)) =
      (table.query positive key).distribution.bind (fun answer =>
        (PMF.uniformOfFintype answer.2.Completion).map
          (fun f => (answer.1, answer.2, f.val))) := by
  classical
  letI : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
  cases found : table.lookup key with
  | some value =>
      have same (f : table.Completion) : f.val key = value :=
        f.property key value found
      simp only [query, found, Draw.distribution, PMF.pure_bind]
      simp_rw [same]
      simp only [afterQuery, found]
  | none =>
      have joint := congrArg
        (fun distribution : PMF (Key → Fin size) => distribution.map
          (fun f => (f key, table.afterQuery key (f key), f)))
        (table.fresh_completion positive key found)
      simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at joint
      have pair (answer : Fin size) (f : (table.program key answer).Completion) :
          f.val key = answer :=
        (table.extend_completionEquiv key found answer f).property
      simp_rw [pair] at joint
      apply joint.trans
      simp only [query, found, Draw.distribution, PMF.bind_map,
        Function.comp_def, afterQuery, program]

/-- The hash query specifies one input and returns one finite output. -/
abbrev hashSpec (Key : Type) (size : Nat) : OracleSpec where
  Query := Key
  Answer := fun _ => Fin size

/-- The eager hash handler records the sparse table that each answer reaches. -/
def hashEager {Key : Type} [DecidableEq Key] {size : Nat} :
    OracleHandler (hashSpec Key size) (HashTable Key size × (Key → Fin size))
  | key, (table, f) => (f key, table.afterQuery key (f key), f)

/-- The sampled hash handler uses only the sparse table. -/
def hashSampled {Key : Type} [DecidableEq Key] {size : Nat} (positive : 0 < size) :
    ∀ query : (hashSpec Key size).Query,
      HashTable Key size → PMF ((hashSpec Key size).Answer query × HashTable Key size)
  | key, table => (table.query positive key).distribution

/-- The kernel retains the table and its full conditional eager function. -/
def hashCompletion {Key : Type} [Fintype Key] [DecidableEq Key] {size : Nat}
    (positive : 0 < size) (table : HashTable Key size) :
    PMF (HashTable Key size × (Key → Fin size)) :=
  letI : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
  (PMF.uniformOfFintype table.Completion).map (fun f => (table, f.val))

/-- The concrete hash step has no additional coupling premise. -/
theorem hash_step {Key : Type} [Fintype Key] [DecidableEq Key] {size : Nat}
    (positive : 0 < size) (key : Key) (table : HashTable Key size) :
    (hashCompletion positive table).map (hashEager key) =
      (hashSampled positive key table).bind (fun answer =>
        (hashCompletion positive answer.2).map (fun eagerState => (answer.1, eagerState))) := by
  simpa only [hashCompletion, hashEager, hashSampled, PMF.map_comp, Function.comp_def] using
    table.query_joint positive key


/-- An empty hash table permits every eager function. -/
def hashEmptyCompletionEquiv {Key : Type} [DecidableEq Key] (size : Nat) :
    HashTable.Completion ([] : HashTable Key size) ≃ (Key → Fin size) where
  toFun := Subtype.val
  invFun f := ⟨f, by intro key value present; simp [List.lookup] at present⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The initial sparse hash law equals the full uniform eager hash law. -/
theorem hash_initial {Key : Type} [Fintype Key] [DecidableEq Key] {size : Nat}
    (positive : 0 < size) :
    letI : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
    hashCompletion positive ([] : HashTable Key size) =
      (PMF.uniformOfFintype (Key → Fin size)).map
        (fun f => (([] : HashTable Key size), f)) := by
  letI : Nonempty (Fin size) := ⟨⟨0, positive⟩⟩
  have law := congrArg
    (fun distribution : PMF (Key → Fin size) => distribution.map
      (fun f => (([] : HashTable Key size), f)))
    (uniform_equiv (hashEmptyCompletionEquiv (Key := Key) size))
  simp only [hashCompletion, PMF.map_comp, Function.comp_def] at law ⊢
  convert law using 1; rfl

end
end Kriterion.ArgoMAC.Security.OperationalOracle
