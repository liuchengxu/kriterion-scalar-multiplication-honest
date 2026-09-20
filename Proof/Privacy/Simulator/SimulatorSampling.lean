import Proof.Privacy.Distribution.PublicDistribution

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography

namespace SimulatorSampling

/-- The program samples bounded integers. The index counts its random draws. -/
inductive Code : Type → Nat → Type 1
  | pure {A : Type} (value : A) : Code A 0
  | draw (size : Nat) (positive : 0 < size) : Code (Fin size) 1
  | bind {A B : Type} {first second : Nat}
      (source : Code A first) (next : A → Code B second) : Code B (first + second)

noncomputable def Code.law {A : Type} {count : Nat} : Code A count → PMF A
  | .pure value => PMF.pure value
  | .draw size positive =>
      letI : NeZero size := ⟨Nat.ne_of_gt positive⟩
      PMF.uniformOfFintype (Fin size)
  | .bind source next => source.law.bind fun value => (next value).law

/-- The interpreter delegates only a bounded integer draw to its random source. -/
def Code.run {A State : Type} {count : Nat}
    (draw : (size : Nat) → 0 < size → State → Fin size × State) :
    Code A count → State → A × State
  | .pure value, state => (value, state)
  | .draw size positive, state => draw size positive state
  | .bind source next, state =>
      let sampled := source.run draw state
      (next sampled.1).run draw sampled.2

/-- This interpreter records the number of random-source calls. -/
def Code.runCount {A State : Type} {count : Nat}
    (draw : (size : Nat) → 0 < size → State → Fin size × State) :
    Code A count → State → (A × State) × Nat
  | .pure value, state => ((value, state), 0)
  | .draw size positive, state => (draw size positive state, 1)
  | .bind source next, state =>
      let first := source.runCount draw state
      let second := (next first.1.1).runCount draw first.1.2
      (second.1, first.2 + second.2)

theorem Code.runCount_correct {A State : Type} {count : Nat}
    (draw : (size : Nat) → 0 < size → State → Fin size × State)
    (code : Code A count) (state : State) :
    (code.runCount draw state).1 = code.run draw state ∧
      (code.runCount draw state).2 = count := by
  induction code generalizing state with
  | pure => exact ⟨rfl, rfl⟩
  | draw => exact ⟨rfl, rfl⟩
  | bind source next first second =>
    obtain ⟨firstEq, firstCount⟩ := first state
    obtain ⟨secondEq, secondCount⟩ := second
      (source.runCount draw state).1.1 (source.runCount draw state).1.2
    constructor
    · change (Code.runCount draw (next (source.runCount draw state).1.1)
        (source.runCount draw state).1.2).1 = _
      rw [secondEq, firstEq]
      rfl
    · simp only [Code.runCount, firstCount, secondCount]

def Code.map {A B : Type} {count : Nat} (f : A → B) (code : Code A count) : Code B count :=
  Nat.add_zero count ▸ Code.bind code (fun value => Code.pure (f value))

theorem Code.map_law {A B : Type} {count : Nat} (f : A → B) (code : Code A count) :
    (code.map f).law = code.law.map f := by
  simp [Code.map, Code.law, PMF.map, Function.comp_def]

def Code.pair {A B : Type} {first second : Nat}
    (a : Code A first) (b : Code B second) : Code (A × B) (second + first) :=
  .bind b fun right => a.map fun left => (left, right)

theorem Code.pair_law {A B : Type} {first second : Nat}
    (a : Code A first) (b : Code B second) :
    (a.pair b).law = b.law.bind fun right => a.law.map fun left => (left, right) := by
  simp [Code.pair, Code.law, Code.map_law]

/-- This predicate checks the sampler's distribution separately from its draw count. -/
def Uniform {A : Type} [Fintype A] [Nonempty A] {count : Nat} (code : Code A count) : Prop :=
  code.law = PMF.uniformOfFintype A

theorem uniform_pair {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    {first second : Nat} {a : Code A first} {b : Code B second}
    (left : Uniform a) (right : Uniform b) : Uniform (a.pair b) := by
  unfold Uniform at *
  rw [Code.pair_law, left, right, ← uniform_prod_eq_bind]

theorem uniform_equiv {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    {count : Nat} {code : Code A count} (uniform : Uniform code) (equivalence : A ≃ B) :
    Uniform (code.map equivalence) := by
  unfold Uniform at *
  rw [Code.map_law, uniform, uniform_map_equiv]

def Code.cast {A : Type} {first second : Nat} (same : first = second)
    (code : Code A first) : Code A second := same ▸ code

@[simp] theorem Code.cast_law {A : Type} {first second : Nat} (same : first = second)
    (code : Code A first) : (code.cast same).law = code.law := by
  cases same
  rfl

def field : Code BaseField 1 :=
  (Code.draw baseFieldModulus (by decide)).map baseFieldFinEquiv

theorem field_uniform : Uniform field := by
  apply uniform_equiv (code := Code.draw baseFieldModulus (by decide))
  rfl

local instance bitsFintype (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) BitVec.equivFin.symm.toEquiv

def bits (width : Nat) : Code (BitVec width) 1 :=
  (Code.draw (2 ^ width) (Nat.two_pow_pos width)).map BitVec.equivFin.symm.toEquiv

theorem bits_uniform (width : Nat) : Uniform (bits width) := by
  apply uniform_equiv (code := Code.draw (2 ^ width) (Nat.two_pow_pos width))
  rfl

set_option exponentiation.threshold 400 in
def quotient : Code HashLiftQuotient 1 :=
  Code.draw hashLiftQuotientCount (by decide)

theorem quotient_uniform : Uniform quotient := rfl

local instance : Nonempty BitAdaptor.Table := ⟨defaultBitAdaptorTable⟩
local instance : Nonempty BitAdaptor.Key := ⟨⟨0, 0⟩⟩
local instance : Nonempty CurvePublicSample := ⟨defaultSimulatorCoin.tableSample.curve⟩
local instance : Nonempty XPublicSample := ⟨defaultRowPublicSample.x⟩
local instance : Nonempty YPublicSample := ⟨defaultRowPublicSample.y⟩
local instance : Nonempty ZPublicSample := ⟨defaultRowPublicSample.z⟩
local instance : Nonempty RowPublicSample := ⟨defaultRowPublicSample⟩
local instance : Nonempty PublicSample := ⟨defaultSimulatorCoin.tableSample⟩
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance : Nonempty SimulatorCoin := ⟨defaultSimulatorCoin⟩
local instance : Nonempty SimulatorOracleCoin := ⟨defaultSimulatorCoin.oracles⟩

attribute [local instance] publicVectorFintype bitAdaptorTableFintype publicBitAdaptorKeyFintype
  publicInputMacKeyFintype

/-- The equivalence appends one value to an array. -/
def vectorPushEquiv (A : Type) (count : Nat) : A × Vector A count ≃ Vector A (count + 1) where
  toFun sample := sample.2.push sample.1
  invFun sample := (sample.back, sample.pop)
  left_inv sample := by simp [Vector.back_eq_getElem]
  right_inv sample := Vector.push_pop_back sample

/-- The sampler constructs its array with one push for each value. -/
def Code.vector {A : Type} {draws : Nat} (code : Code A draws) :
    (count : Nat) → Code (Vector A count) (count * draws)
  | 0 => (Code.pure #v[]).cast (Nat.zero_mul draws).symm
  | count + 1 =>
      ((code.pair (code.vector count)).map (vectorPushEquiv A count)).cast
        (Nat.succ_mul count draws).symm

theorem Code.vector_uniform {A : Type} [Fintype A] [Nonempty A] {draws : Nat}
    (code : Code A draws) (uniform : Uniform code) (count : Nat) : Uniform (code.vector count) := by
  induction count with
  | zero =>
    unfold Uniform
    apply PMF.ext
    intro result
    haveI : Subsingleton (Vector A 0) := ⟨fun a b => by
      apply Vector.ext
      intro index bound
      omega⟩
    have card : Fintype.card (Vector A 0) = 1 :=
      Fintype.card_eq_one_iff.mpr ⟨#v[], fun _ => Subsingleton.elim _ _⟩
    have only : result = #v[] := Subsingleton.elim _ _
    subst result
    simp [Code.vector, Code.law, PMF.uniformOfFintype_apply, card]
  | succ count inductionHypothesis =>
    unfold Uniform
    rw [Code.vector, Code.cast_law]
    exact uniform_equiv (uniform_pair uniform inductionHypothesis) _

/-- The sampler exposes its array through a direct indexed getter. -/
def Code.arrayFunction {A : Type} {draws : Nat} (code : Code A draws) (count : Nat) :
    Code (Fin count → A) (count * draws) :=
  (code.vector count).map vectorFunctionEquiv.symm

theorem Code.arrayFunction_uniform {A : Type} [Fintype A] [Nonempty A] {draws : Nat}
    (code : Code A draws) (uniform : Uniform code) (count : Nat) :
    Uniform (code.arrayFunction count) :=
  uniform_equiv (code.vector_uniform uniform count) _

def tableEquiv : BitVec 256 ≃ BitAdaptor.Table where
  toFun value := ⟨value⟩
  invFun value := value.trueRow
  left_inv _ := rfl
  right_inv _ := rfl

def table : Code BitAdaptor.Table 1 := (bits 256).map tableEquiv

theorem table_uniform : Uniform table := uniform_equiv (bits_uniform 256) _

 abbrev GateData (coefficients gates : Nat) :=
  (Fin coefficients → BaseField) × ((Fin gates → Vector BitAdaptor.Table coordinateBitCount) ×
    ((Fin gates → Fin coordinateBitCount → HashLiftQuotient) ×
      (Fin gates → Fin coordinateBitCount → BaseField)))

/-- These arrays support direct indexed reads in the gate schedule. -/
abbrev GateArrays (coefficients gates : Nat) :=
  Vector BaseField coefficients × ((Vector (Vector BitAdaptor.Table coordinateBitCount) gates) ×
    ((Vector (Vector HashLiftQuotient coordinateBitCount) gates) ×
      Vector (Vector BaseField coordinateBitCount) gates))

def gateArraysEquiv (coefficients gates : Nat) :
    GateArrays coefficients gates ≃ GateData coefficients gates :=
  Equiv.prodCongr vectorFunctionEquiv.symm
    (Equiv.prodCongr vectorFunctionEquiv.symm
      (Equiv.prodCongr
        (vectorFunctionEquiv.symm.trans (Equiv.piCongrRight fun _ => vectorFunctionEquiv.symm))
        (vectorFunctionEquiv.symm.trans (Equiv.piCongrRight fun _ => vectorFunctionEquiv.symm))))

def gateArrays (coefficients gates : Nat) : Code (GateArrays coefficients gates)
    (coefficients + 3 * gates * coordinateBitCount) :=
  ((field.vector coefficients).pair
    (((table.vector coordinateBitCount).vector gates).pair
      (((quotient.vector coordinateBitCount).vector gates).pair
        ((field.vector coordinateBitCount).vector gates)))).cast (by ring)

theorem gateArrays_uniform (coefficients gates : Nat) : Uniform (gateArrays coefficients gates) := by
  unfold Uniform gateArrays
  rw [Code.cast_law]
  exact uniform_pair (field.vector_uniform field_uniform coefficients)
    (uniform_pair (((table.vector coordinateBitCount).vector_uniform
      (table.vector_uniform table_uniform coordinateBitCount)) gates)
      (uniform_pair
        ((quotient.vector coordinateBitCount).vector_uniform
          (quotient.vector_uniform quotient_uniform coordinateBitCount) gates)
        ((field.vector coordinateBitCount).vector_uniform
          (field.vector_uniform field_uniform coordinateBitCount) gates)))

def gateData (coefficients gates : Nat) : Code (GateData coefficients gates)
    (coefficients + 3 * gates * coordinateBitCount) :=
  (gateArrays coefficients gates).map (gateArraysEquiv coefficients gates)

theorem gateData_uniform (coefficients gates : Nat) : Uniform (gateData coefficients gates) :=
  uniform_equiv (gateArrays_uniform coefficients gates) _

def curveEquiv : GateData 3 5 ≃ CurvePublicSample where
  toFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  invFun x := (x.coefficients, x.tables, x.quotients, x.targets)
  left_inv _ := rfl
  right_inv _ := rfl

def xEquiv : GateData 5 4 ≃ XPublicSample where
  toFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  invFun x := (x.coefficients, x.tables, x.quotients, x.targets)
  left_inv _ := rfl
  right_inv _ := rfl

def yEquiv : GateData 4 3 ≃ YPublicSample where
  toFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  invFun x := (x.coefficients, x.tables, x.quotients, x.targets)
  left_inv _ := rfl
  right_inv _ := rfl

def zEquiv : GateData 5 5 ≃ ZPublicSample where
  toFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  invFun x := (x.coefficients, x.tables, x.quotients, x.targets)
  left_inv _ := rfl
  right_inv _ := rfl

def rowEquiv : XPublicSample × (YPublicSample × ZPublicSample) ≃ RowPublicSample where
  toFun x := ⟨x.1, x.2.1, x.2.2⟩
  invFun x := (x.x, x.y, x.z)
  left_inv _ := rfl
  right_inv _ := rfl

def row : Code RowPublicSample 9158 :=
  (((gateData 5 4).map xEquiv).pair
    (((gateData 4 3).map yEquiv).pair ((gateData 5 5).map zEquiv))).map rowEquiv

theorem row_uniform : Uniform row :=
  uniform_equiv (uniform_pair (uniform_equiv (gateData_uniform 5 4) _)
    (uniform_pair (uniform_equiv (gateData_uniform 4 3) _)
      (uniform_equiv (gateData_uniform 5 5) _))) _

def publicEquiv : CurvePublicSample × Vector RowPublicSample FieldMacToECMac.outputMacCount ≃
    PublicSample where
  toFun x := ⟨x.1, x.2⟩
  invFun x := (x.curve, x.points)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The public sample needs 837191 bounded integer draws: 91 rows of 9158 draws plus the
curve gate data. It samples no oracle tables. -/
def publicSample : Code PublicSample 837191 :=
  (((gateData 3 5).map curveEquiv).pair (row.vector FieldMacToECMac.outputMacCount)).map publicEquiv

theorem public_uniform : Uniform publicSample :=
  uniform_equiv (uniform_pair (uniform_equiv (gateData_uniform 3 5) _)
    (row.vector_uniform row_uniform _)) _

def keyEquiv : Block × Block ≃ BitAdaptor.Key where
  toFun x := ⟨x.1, x.2⟩
  invFun x := (x.falseLabel, x.trueLabel)
  left_inv _ := rfl
  right_inv _ := rfl

def key : Code BitAdaptor.Key 2 := ((bits 128).pair (bits 128)).map keyEquiv

theorem key_uniform : Uniform key :=
  uniform_equiv (uniform_pair (bits_uniform 128) (bits_uniform 128)) _

def inputKeyEquiv :
    Vector BitAdaptor.Key coordinateBitCount × Vector BitAdaptor.Key coordinateBitCount ≃ InputMacKey where
  toFun x := ⟨x.1, x.2⟩
  invFun x := (x.x, x.y)
  left_inv _ := rfl
  right_inv _ := rfl

def inputKey : Code InputMacKey 1016 :=
  ((key.vector coordinateBitCount).pair (key.vector coordinateBitCount)).map inputKeyEquiv

theorem inputKey_uniform : Uniform inputKey :=
  uniform_equiv (uniform_pair (key.vector_uniform key_uniform _) (key.vector_uniform key_uniform _)) _

 abbrev OfflineCoin := PublicSample × (InputMacKey × BaseField)

/-- This sampler constructs the complete private coin outside the oracle environment. -/
def offline : Code OfflineCoin 838208 := publicSample.pair (inputKey.pair field)

theorem offline_uniform : Uniform offline :=
  uniform_pair public_uniform (uniform_pair inputKey_uniform field_uniform)

def coinEquiv : OfflineCoin × SimulatorOracleCoin ≃ SimulatorCoin where
  toFun x := ⟨x.1.1, x.2, x.1.2.1, x.1.2.2⟩
  invFun x := ((x.tableSample, x.inputKey, x.bridgeKey), x.oracles)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The operational private sampler has the exact law of the original private coin. -/
theorem offline_with_oracles :
    (PMF.uniformOfFintype SimulatorOracleCoin).bind (fun oracles =>
      offline.law.map (fun coin => coinEquiv (coin, oracles))) =
        PMF.uniformOfFintype SimulatorCoin := by
  rw [offline_uniform]
  have law := uniform_map_equiv coinEquiv
  rw [uniform_prod_eq_bind, PMF.map_bind] at law
  simpa only [PMF.map_comp, Function.comp_def] using law

/-- This bound applies to every draw on every execution path. -/
def Code.DrawSizeLe (maximum : Nat) {A : Type} {count : Nat} : Code A count → Prop
  | .pure _ => True
  | .draw size _ => size ≤ maximum
  | .bind source next => source.DrawSizeLe maximum ∧ ∀ value, (next value).DrawSizeLe maximum

theorem Code.cast_drawSizeLe {A : Type} {first second maximum : Nat}
    (same : first = second) (code : Code A first) (bounded : code.DrawSizeLe maximum) :
    (code.cast same).DrawSizeLe maximum := by
  cases same
  exact bounded

theorem Code.map_drawSizeLe {A B : Type} {count maximum : Nat}
    (f : A → B) (code : Code A count) (bounded : code.DrawSizeLe maximum) :
    (code.map f).DrawSizeLe maximum := ⟨bounded, fun _ => trivial⟩

theorem Code.pair_drawSizeLe {A B : Type} {first second maximum : Nat}
    (a : Code A first) (b : Code B second)
    (left : a.DrawSizeLe maximum) (right : b.DrawSizeLe maximum) :
    (a.pair b).DrawSizeLe maximum := ⟨right, fun _ => a.map_drawSizeLe _ left⟩

theorem Code.vector_drawSizeLe {A : Type} {draws maximum : Nat}
    (code : Code A draws) (bounded : code.DrawSizeLe maximum) (count : Nat) :
    (code.vector count).DrawSizeLe maximum := by
  induction count with
  | zero => exact Code.cast_drawSizeLe _ _ trivial
  | succ count inductionHypothesis =>
    exact Code.cast_drawSizeLe _ _
      (Code.map_drawSizeLe _ _ (Code.pair_drawSizeLe _ _ bounded inductionHypothesis))

theorem Code.arrayFunction_drawSizeLe {A : Type} {draws maximum : Nat}
    (code : Code A draws) (bounded : code.DrawSizeLe maximum) (count : Nat) :
    (code.arrayFunction count).DrawSizeLe maximum :=
  Code.map_drawSizeLe _ _ (code.vector_drawSizeLe bounded count)

theorem field_drawSizeLe : field.DrawSizeLe (2 ^ 256) :=
  Code.map_drawSizeLe _ _ (by change baseFieldModulus ≤ 2 ^ 256; decide)

theorem bits_drawSizeLe {width : Nat} (bounded : width ≤ 256) :
    (bits width).DrawSizeLe (2 ^ 256) :=
  Code.map_drawSizeLe _ _ (Nat.pow_le_pow_right (by decide) bounded)

set_option exponentiation.threshold 400 in
theorem quotient_drawSizeLe : quotient.DrawSizeLe (2 ^ 256) := by
  change hashLiftQuotientCount ≤ 2 ^ 256
  decide

theorem gateArrays_drawSizeLe (coefficients gates : Nat) :
    (gateArrays coefficients gates).DrawSizeLe (2 ^ 256) := by
  apply Code.cast_drawSizeLe
  exact Code.pair_drawSizeLe _ _ (field.vector_drawSizeLe field_drawSizeLe _)
    (Code.pair_drawSizeLe _ _
      (((table.vector coordinateBitCount).vector_drawSizeLe
        (Code.vector_drawSizeLe _ (Code.map_drawSizeLe _ _ (bits_drawSizeLe (by decide))) _)) _)
      (Code.pair_drawSizeLe _ _
        ((quotient.vector coordinateBitCount).vector_drawSizeLe
          (quotient.vector_drawSizeLe quotient_drawSizeLe _) _)
        ((field.vector coordinateBitCount).vector_drawSizeLe
          (field.vector_drawSizeLe field_drawSizeLe _) _)))


theorem gateData_drawSizeLe (coefficients gates : Nat) :
    (gateData coefficients gates).DrawSizeLe (2 ^ 256) :=
  Code.map_drawSizeLe _ _ (gateArrays_drawSizeLe coefficients gates)

theorem row_drawSizeLe : row.DrawSizeLe (2 ^ 256) :=
  Code.map_drawSizeLe _ _ (Code.pair_drawSizeLe _ _
    (Code.map_drawSizeLe _ _ (gateData_drawSizeLe _ _))
    (Code.pair_drawSizeLe _ _
      (Code.map_drawSizeLe _ _ (gateData_drawSizeLe _ _))
      (Code.map_drawSizeLe _ _ (gateData_drawSizeLe _ _))))

/-- Every private draw uses a range of at most 256 bits. -/
theorem offline_drawSizeLe : offline.DrawSizeLe (2 ^ 256) := by
  have keyBound : key.DrawSizeLe (2 ^ 256) := Code.map_drawSizeLe _ _
    (Code.pair_drawSizeLe _ _ (bits_drawSizeLe (by decide)) (bits_drawSizeLe (by decide)))
  apply Code.pair_drawSizeLe
  · exact Code.map_drawSizeLe _ _ (Code.pair_drawSizeLe _ _
      (Code.map_drawSizeLe _ _ (gateData_drawSizeLe _ _)) (row.vector_drawSizeLe row_drawSizeLe _))
  · apply Code.pair_drawSizeLe
    · exact Code.map_drawSizeLe _ _ (Code.pair_drawSizeLe _ _
        (key.vector_drawSizeLe keyBound _) (key.vector_drawSizeLe keyBound _))
    · exact field_drawSizeLe

/-- The successor enumeration samples each nonzero field value exactly once. -/
def nonzeroEquiv : Fin (baseFieldModulus - 1) ≃ NonZeroBase where
  toFun index := {
    value := (index.val + 1 : Nat)
    nonzero := by
      have bound : index.val + 1 < baseFieldModulus := by have := index.isLt; omega
      intro zero
      have value := congrArg (fun x : BaseField => x.val) zero
      change ((index.val + 1 : Nat) : BaseField).val = (0 : BaseField).val at value
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt bound, ZMod.val_zero] at value
      omega }
  invFun value := ⟨value.value.val - 1, by
    have bound := value.value.val_lt
    have positive : 0 < value.value.val := Nat.pos_of_ne_zero
      (fun zero => value.nonzero ((ZMod.val_eq_zero _).mp zero))
    omega⟩
  left_inv index := by
    apply Fin.ext
    have bound : index.val + 1 < baseFieldModulus := by have := index.isLt; omega
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt bound]
    omega
  right_inv value := by
    have positive : 0 < value.value.val := Nat.pos_of_ne_zero
      (fun zero => value.nonzero ((ZMod.val_eq_zero _).mp zero))
    have same : value.value.val - 1 + 1 = value.value.val := by omega
    cases value with
    | mk value nonzero =>
      simp only [NonZeroBase.mk.injEq]
      dsimp only at same ⊢
      rw [same, ZMod.natCast_zmod_val]

/-- One bounded draw gives one nonzero homogeneous scale. -/
def scale : Code NonZeroBase 1 :=
  (Code.draw (baseFieldModulus - 1) (by decide)).map nonzeroEquiv

theorem scale_uniform [FieldCertificate] : Uniform scale := by
  letI : Nonempty (Fin (baseFieldModulus - 1)) := ⟨⟨0, by decide⟩⟩
  apply uniform_equiv (code := Code.draw (baseFieldModulus - 1) (by decide))
  rfl

 theorem scale_drawSizeLe : scale.DrawSizeLe (2 ^ 256) :=
  Code.map_drawSizeLe _ _ (by change baseFieldModulus - 1 ≤ 2 ^ 256; decide)

@[simp] theorem Code.cast_run {A State : Type} {first second : Nat} (same : first = second)
    (code : Code A first) (draw : (size : Nat) → 0 < size → State → Fin size × State)
    (state : State) : (code.cast same).run draw state = code.run draw state := by
  cases same
  rfl

@[simp] theorem Code.map_run {A B State : Type} {count : Nat} (f : A → B)
    (code : Code A count) (draw : (size : Nat) → 0 < size → State → Fin size × State)
    (state : State) : (code.map f).run draw state =
      (f (code.run draw state).1, (code.run draw state).2) := by
  simp [Code.map, Code.run]

/-- The interpreter counts array pushes. The source sampler keeps its own cost. -/
def vectorRun {A State : Type} {draws : Nat} (code : Code A draws)
    (draw : (size : Nat) → 0 < size → State → Fin size × State) :
    (count : Nat) → State → (Vector A count × State) × Nat
  | 0, state => ((#v[], state), 0)
  | count + 1, state =>
    let previous := vectorRun code draw count state
    let value := code.run draw previous.1.2
    ((previous.1.1.push value.1, value.2), previous.2 + 1)

/-- The array interpreter has the same result and makes exactly count pushes. -/
theorem vectorRun_correct {A State : Type} {draws : Nat} (code : Code A draws)
    (draw : (size : Nat) → 0 < size → State → Fin size × State) (count : Nat) (state : State) :
    (vectorRun code draw count state).1 = (code.vector count).run draw state ∧
      (vectorRun code draw count state).2 = count := by
  induction count with
  | zero => simp [vectorRun, Code.vector, Code.run]
  | succ count ih =>
    rcases ih with ⟨result, cost⟩
    simp only [vectorRun, Code.vector, Code.cast_run, Code.pair, Code.run, Code.map_run]
    simp only [result, cost, vectorPushEquiv, Equiv.coe_fn_mk]
    exact ⟨trivial, trivial⟩

end SimulatorSampling
end Kriterion.ArgoMAC.Security
