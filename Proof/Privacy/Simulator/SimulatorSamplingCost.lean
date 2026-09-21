import Proof.Privacy.Simulator.SimulatorScheduleCost
import Proof.Privacy.Simulator.OperationalSimulator

namespace Kriterion.ArgoMAC.Security.SimulatorSamplingCost
open BN254 Cryptography SimulatorSampling SimulatorScheduleCost
set_option maxRecDepth 4096

/-- This predicate bounds the local charge on every random tape. -/
def Bounded {A : Type} {draws : Nat} (code : Code (A × Nat) draws) (bound : Nat) : Prop :=
  ∀ (Seed : Type) (random : (size : Nat) → 0 < size → Seed → Fin size × Seed) (seed : Seed),
    (code.run random seed).1.2 ≤ bound

/-- This constructor joins two sampled values and charges the value record. -/
def pair {A B : Type} {first second : Nat}
    (left : Code (A × Nat) first) (right : Code (B × Nat) second) :
    Code ((A × B) × Nat) (second + first) :=
  (left.pair right).map fun values => ((values.1.1, values.2.1), values.1.2 + values.2.2 + 2)

theorem pair_law {A B : Type} {first second : Nat}
    (left : Code (A × Nat) first) (right : Code (B × Nat) second) :
    (pair left right).law.map Prod.fst =
      (right.law.map Prod.fst).bind (fun b => (left.law.map Prod.fst).map fun a => (a, b)) := by
  simp only [pair, Code.map_law, Code.pair_law, PMF.map_bind, PMF.map_comp,
    PMF.bind_map, Function.comp_def]

theorem pair_bound {A B : Type} {first second l r : Nat}
    (left : Code (A × Nat) first) (right : Code (B × Nat) second)
    (hl : Bounded left l) (hr : Bounded right r) : Bounded (pair left right) (l + r + 2) := by
  intro Seed random seed
  have a := hl Seed random (right.run random seed).2
  have b := hr Seed random seed
  simp only [pair, Code.map_run, Code.pair, Code.run]
  omega

/-- Each recursion step appends one value to the sampled array. -/
def vector {A : Type} {draws : Nat} (code : Code (A × Nat) draws) :
    (count : Nat) → Code (Vector A count × Nat) (count * draws)
  | 0 => (Code.pure (#v[], 0)).cast (Nat.zero_mul draws).symm
  | count + 1 =>
    ((code.pair (vector code count)).map fun values =>
      (values.2.1.push values.1.1, values.2.2 + values.1.2 + 1)).cast (Nat.succ_mul count draws).symm

theorem vector_law {A : Type} {draws : Nat} (code : Code (A × Nat) draws)
    (reference : Code A draws) (same : code.law.map Prod.fst = reference.law) (count : Nat) :
    (vector code count).law.map Prod.fst = (reference.vector count).law := by
  induction count with
  | zero => simp [vector, Code.vector, Code.law, PMF.pure_map]
  | succ count ih =>
    simp only [vector, Code.cast_law, Code.map_law, Code.pair_law,
      PMF.map_bind, PMF.map_comp, Function.comp_def, Code.vector]
    have projected := congrArg (fun p : PMF (Vector A count) =>
      p.bind fun rest => reference.law.map (fun value => rest.push value)) ih
    simp only [PMF.bind_map] at projected
    have mappedSame (rest : Vector A count) :
        code.law.map (fun value => rest.push value.1) = reference.law.map rest.push := by
      rw [← same, PMF.map_comp]
      rfl
    simp_rw [mappedSame]
    simpa only [vectorPushEquiv, Equiv.coe_fn_mk, Function.comp_def] using projected

theorem vector_bound {A : Type} {draws limit : Nat} (code : Code (A × Nat) draws)
    (bounded : Bounded code limit) (count : Nat) :
    Bounded (vector code count) (count * (limit + 1)) := by
  induction count with
  | zero => intro Seed random seed; simp [vector, Code.run]
  | succ count ih =>
    intro Seed random seed
    have a := ih Seed random seed
    have b := bounded Seed random ((vector code count).run random seed).2
    simp only [vector, Code.cast_run, Code.map_run, Code.pair, Code.run, Code.map_run]
    nlinarith

private def mapped {A B : Type} {draws : Nat} (code : Code (A × Nat) draws)
    (f : A → B) (charge : Nat) : Code (B × Nat) draws :=
  code.map fun value => (f value.1, value.2 + charge)

private theorem mapped_law {A B : Type} {draws : Nat} (code : Code (A × Nat) draws)
    (f : A → B) (charge : Nat) :
    (mapped code f charge).law.map Prod.fst = (code.law.map Prod.fst).map f := by
  simp [mapped, Code.map_law, PMF.map_comp, Function.comp_def]

private theorem mapped_bound {A B : Type} {draws limit : Nat} (code : Code (A × Nat) draws)
    (bounded : Bounded code limit) (f : A → B) (charge : Nat) :
    Bounded (mapped code f charge) (limit + charge) := by
  intro Seed random seed
  simpa only [mapped, Code.map_run] using Nat.add_le_add_right (bounded Seed random seed) charge

private theorem cast_bound {A : Type} {first second limit : Nat} (same : first = second)
    (code : Code (A × Nat) first) (bounded : Bounded code limit) :
    Bounded (code.cast same) limit := by cases same; exact bounded

/-- The field callback charges its finite-residue conversion and result construction. -/
def fieldWithCost : Code (BaseField × Nat) 1 := field.map fun value => (value, 2)
/-- The block callback charges its finite-word conversion and result construction. -/
def bitsWithCost (width : Nat) : Code (BitVec width × Nat) 1 := (bits width).map fun value => (value, 2)
/-- The quotient draw already has the required finite type. -/
def quotientWithCost : Code (HashLiftQuotient × Nat) 1 := quotient.map fun value => (value, 1)
/-- The table constructor stores one sampled word. -/
def tableWithCost : Code (BitAdaptor.Table × Nat) 1 := mapped (bitsWithCost 256) tableEquiv 1

theorem field_law : fieldWithCost.law.map Prod.fst = field.law := by
  simp only [fieldWithCost, Code.map_law, PMF.map_comp, Function.comp_def ]
  exact PMF.map_id _
theorem bits_law (width : Nat) : (bitsWithCost width).law.map Prod.fst = (bits width).law := by
  simp only [bitsWithCost, Code.map_law, PMF.map_comp, Function.comp_def ]
  exact PMF.map_id _
theorem quotient_law : quotientWithCost.law.map Prod.fst = quotient.law := by
  simp only [quotientWithCost, Code.map_law, PMF.map_comp, Function.comp_def ]
  exact PMF.map_id _
theorem table_law : tableWithCost.law.map Prod.fst = table.law := by rw [tableWithCost, mapped_law, bits_law]; exact (Code.map_law _ _).symm

theorem field_bound : Bounded fieldWithCost 2 := by intro Seed random seed; simp [fieldWithCost, Code.map_run]
theorem bits_bound (width : Nat) : Bounded (bitsWithCost width) 2 := by intro Seed random seed; simp [bitsWithCost, Code.map_run]
theorem quotient_bound : Bounded quotientWithCost 1 := by intro Seed random seed; simp [quotientWithCost, Code.map_run]
theorem table_bound : Bounded tableWithCost 3 := mapped_bound _ (bits_bound 256) _ _

/-- This sampler counts every nested target, quotient, and table array push. -/
def gateWithCost (coefficients gates : Nat) : Code (GateArrays coefficients gates × Nat)
    (coefficients + 3 * gates * coordinateBitCount) :=
  (pair (vector fieldWithCost coefficients)
    (pair (vector (vector tableWithCost coordinateBitCount) gates)
      (pair (vector (vector quotientWithCost coordinateBitCount) gates)
        (vector (vector fieldWithCost coordinateBitCount) gates)))).cast (by ring)

theorem gate_law (coefficients gates : Nat) :
    (gateWithCost coefficients gates).law.map Prod.fst = (gateArrays coefficients gates).law := by
  simp only [gateWithCost, Code.cast_law, pair_law, vector_law _ _ field_law,
    gateArrays,
    Code.pair_law]
  rw [vector_law _ _ (vector_law _ _ table_law _) _,
    vector_law _ _ (vector_law _ _ quotient_law _) _,
    vector_law _ _ (vector_law _ _ field_law _) _]

theorem gate_bound (coefficients gates : Nat) :
    Bounded (gateWithCost coefficients gates)
      (3 * coefficients + gates * (9 * coordinateBitCount + 3) + 6) := by
  have bound := pair_bound _ _ (vector_bound _ field_bound coefficients)
    (pair_bound _ _ (vector_bound _ (vector_bound _ table_bound coordinateBitCount) gates)
      (pair_bound _ _ (vector_bound _ (vector_bound _ quotient_bound coordinateBitCount) gates)
        (vector_bound _ (vector_bound _ field_bound coordinateBitCount) gates)))
  apply cast_bound
  convert bound using 1
  ring

/-- The key sampler constructs each pair and each coordinate array. -/
def keyWithCost : Code (BitAdaptor.Key × Nat) 2 :=
  mapped (pair (bitsWithCost 128) (bitsWithCost 128)) keyEquiv 1

def inputKeyWithCost : Code (InputMacKey × Nat) 1016 :=
  mapped (pair (vector keyWithCost coordinateBitCount) (vector keyWithCost coordinateBitCount))
    inputKeyEquiv 1

theorem key_law : keyWithCost.law.map Prod.fst = key.law := by
  simp only [keyWithCost, mapped_law, pair_law, bits_law, key, Code.map_law, Code.pair_law]

theorem inputKey_law : inputKeyWithCost.law.map Prod.fst = inputKey.law := by
  simp only [inputKeyWithCost, mapped_law, pair_law, vector_law _ _ key_law,
    inputKey, Code.map_law, Code.pair_law]

theorem key_bound : Bounded keyWithCost 7 :=
  mapped_bound _ (pair_bound _ _ (bits_bound 128) (bits_bound 128)) _ _

theorem inputKey_bound : Bounded inputKeyWithCost 4067 :=
  mapped_bound _ (pair_bound _ _ (vector_bound _ key_bound _) (vector_bound _ key_bound _)) _ _

/-- The counted offline sampler retains all backing arrays. -/
def rowWithCost : Code (RowArrays × Nat) 9158 :=
  pair (gateWithCost 5 4) (pair (gateWithCost 4 3) (gateWithCost 5 5))

def publicWithCost : Code (PublicArrays × Nat) 837191 :=
  pair (gateWithCost 3 5) (vector rowWithCost FieldMacToECMac.outputMacCount)

def offlineWithCost : Code (OfflineArrays × Nat) 838208 :=
  pair publicWithCost (pair inputKeyWithCost fieldWithCost)

theorem row_law : rowWithCost.law.map Prod.fst = rowArrays.law := by
  simp only [rowWithCost, pair_law, gate_law, rowArrays, Code.pair_law]

theorem public_law : publicWithCost.law.map Prod.fst = publicArrays.law := by
  simp only [publicWithCost, pair_law, gate_law, vector_law _ _ row_law,
    publicArrays, Code.pair_law]

/-- Erasing the counter gives exactly the existing offline distribution. -/
theorem offline_law : offlineWithCost.law.map Prod.fst = offlineArrays.law := by
  simp only [offlineWithCost, pair_law, public_law, inputKey_law, field_law,
    offlineArrays, Code.pair_law]

theorem row_bound : Bounded rowWithCost 27532 :=
  pair_bound _ _ (gate_bound 5 4) (pair_bound _ _ (gate_bound 4 3) (gate_bound 5 5))

theorem public_bound : Bounded publicWithCost 2516965 :=
  pair_bound _ _ (gate_bound 3 5) (vector_bound _ row_bound FieldMacToECMac.outputMacCount)

/-- This bound includes every sampled array push and every value-record constructor. -/
theorem offline_bound : Bounded offlineWithCost 2521038 :=
  pair_bound _ _ public_bound (pair_bound _ _ inputKey_bound field_bound)

abbrev OnlineCoin [FieldCertificate] := (Fin 90 → Point) × (Fin FieldMacToECMac.outputMacCount → NonZeroBase)

/-- Each scalar round charges division, remainder, a test, and three loop operations.
The addition count comes from the executed group algorithm. -/
def pointWithCost [FieldCertificate] : Code (Point × Nat) 1 :=
  scalar.map fun value =>
    let result := binaryPointMulWithCost 254 value.val standardGenerator
    (result.1, result.2 + 6 * 254 + 3)

def scaleWithCost : Code (NonZeroBase × Nat) 1 := scale.map fun value => (value, 4)

/-- The getter constructor retains the sampled array without copying it. -/
def arrayFunction {A : Type} {draws : Nat} (code : Code (A × Nat) draws) (count : Nat) :
    Code ((Fin count → A) × Nat) (count * draws) :=
  mapped (vector code count) (fun values => values.get) 1

def onlineWithCost [FieldCertificate] : Code (OnlineCoin × Nat) 181 :=
  pair (arrayFunction pointWithCost 90) (arrayFunction scaleWithCost FieldMacToECMac.outputMacCount)

theorem point_law [FieldCertificate] : pointWithCost.law.map Prod.fst = point.law := by
  simp only [pointWithCost, point, Code.map_law, PMF.map_comp, Function.comp_def]
  congr 1
  funext value
  exact (samplePoint_groupAdditions value).1

theorem scale_law : scaleWithCost.law.map Prod.fst = scale.law := by
  simp only [scaleWithCost, Code.map_law, PMF.map_comp, Function.comp_def]
  exact PMF.map_id scale.law

theorem arrayFunction_law {A : Type} {draws : Nat} (code : Code (A × Nat) draws)
    (reference : Code A draws) (same : code.law.map Prod.fst = reference.law) (count : Nat) :
    (arrayFunction code count).law.map Prod.fst = (reference.arrayFunction count).law := by
  rw [arrayFunction, mapped_law, vector_law _ _ same]
  exact (Code.map_law _ _).symm

/-- Erasing the counter gives exactly the existing online distribution. -/
theorem online_law [FieldCertificate] : onlineWithCost.law.map Prod.fst = online.law := by
  simp only [onlineWithCost, pair_law, arrayFunction_law _ _ point_law,
    arrayFunction_law _ _ scale_law, online, Code.pair_law]

theorem point_bound [FieldCertificate] : Bounded pointWithCost 2035 := by
  intro Seed random seed
  simp only [pointWithCost, Code.map_run]
  have bound := (samplePoint_groupAdditions (scalar.run random seed).1).2
  omega

theorem scale_bound : Bounded scaleWithCost 4 := by
  intro Seed random seed
  simp only [scaleWithCost, Code.map_run]
  exact Nat.le_refl _

theorem arrayFunction_bound {A : Type} {draws limit : Nat} (code : Code (A × Nat) draws)
    (bounded : Bounded code limit) (count : Nat) :
    Bounded (arrayFunction code count) (count * (limit + 1) + 1) :=
  mapped_bound _ (vector_bound _ bounded count) _ _

/-- The online bound includes 90 scalar loops and at most 45720 group additions. -/
theorem online_bound [FieldCertificate] : Bounded onlineWithCost 183699 :=
  pair_bound _ _ (arrayFunction_bound _ point_bound 90) (arrayFunction_bound _ scale_bound FieldMacToECMac.outputMacCount)

private theorem pair_size {A B : Type} {first second : Nat}
    (left : Code (A × Nat) first) (right : Code (B × Nat) second)
    (hl : left.DrawSizeLe (2 ^ 256)) (hr : right.DrawSizeLe (2 ^ 256)) :
    (pair left right).DrawSizeLe (2 ^ 256) :=
  Code.map_drawSizeLe _ _ (Code.pair_drawSizeLe _ _ hl hr)

private theorem vector_size {A : Type} {draws : Nat} (code : Code (A × Nat) draws)
    (bounded : code.DrawSizeLe (2 ^ 256)) (count : Nat) :
    (vector code count).DrawSizeLe (2 ^ 256) := by
  induction count with
  | zero => exact Code.cast_drawSizeLe _ _ trivial
  | succ count ih =>
    exact Code.cast_drawSizeLe _ _ (Code.map_drawSizeLe _ _ (Code.pair_drawSizeLe _ _ bounded ih))

private theorem mapped_size {A B : Type} {draws : Nat} (code : Code (A × Nat) draws)
    (bounded : code.DrawSizeLe (2 ^ 256)) (f : A → B) (charge : Nat) :
    (mapped code f charge).DrawSizeLe (2 ^ 256) := Code.map_drawSizeLe _ _ bounded

private theorem field_size : fieldWithCost.DrawSizeLe (2 ^ 256) := Code.map_drawSizeLe _ _ field_drawSizeLe
private theorem bits_size (width : Nat) (bounded : width ≤ 256) :
    (bitsWithCost width).DrawSizeLe (2 ^ 256) := Code.map_drawSizeLe _ _ (bits_drawSizeLe bounded)
private theorem quotient_size : quotientWithCost.DrawSizeLe (2 ^ 256) := Code.map_drawSizeLe _ _ quotient_drawSizeLe
private theorem table_size : tableWithCost.DrawSizeLe (2 ^ 256) := mapped_size _ (bits_size 256 (by decide)) _ _

private theorem gate_size (coefficients gates : Nat) :
    (gateWithCost coefficients gates).DrawSizeLe (2 ^ 256) :=
  Code.cast_drawSizeLe _ _ (pair_size _ _ (vector_size _ field_size coefficients)
    (pair_size _ _ (vector_size _ (vector_size _ table_size coordinateBitCount) gates)
      (pair_size _ _ (vector_size _ (vector_size _ quotient_size coordinateBitCount) gates)
        (vector_size _ (vector_size _ field_size coordinateBitCount) gates))))

private theorem key_size : keyWithCost.DrawSizeLe (2 ^ 256) :=
  mapped_size _ (pair_size _ _ (bits_size 128 (by decide)) (bits_size 128 (by decide))) _ _

/-- Every counted offline draw has the same finite range bound. -/
theorem offline_size : offlineWithCost.DrawSizeLe (2 ^ 256) :=
  pair_size _ _
    (pair_size _ _ (gate_size 3 5)
      (vector_size _ (pair_size _ _ (gate_size 5 4) (pair_size _ _ (gate_size 4 3) (gate_size 5 5))) _))
    (pair_size _ _ (mapped_size _
      (pair_size _ _ (vector_size _ key_size _) (vector_size _ key_size _)) _ _) field_size)

/-- Every counted online draw has the same finite range bound. -/
theorem online_size [FieldCertificate] : onlineWithCost.DrawSizeLe (2 ^ 256) := by
  have pointSize : pointWithCost.DrawSizeLe (2 ^ 256) :=
    Code.map_drawSizeLe _ _ (Code.map_drawSizeLe _ _ (by change scalarFieldModulus ≤ 2 ^ 256; decide))
  have scaleSize : scaleWithCost.DrawSizeLe (2 ^ 256) := Code.map_drawSizeLe _ _ scale_drawSizeLe
  exact pair_size _ _ (mapped_size _ (vector_size _ pointSize 90) _ _)
    (mapped_size _ (vector_size _ scaleSize FieldMacToECMac.outputMacCount) _ _)

end Kriterion.ArgoMAC.Security.SimulatorSamplingCost
