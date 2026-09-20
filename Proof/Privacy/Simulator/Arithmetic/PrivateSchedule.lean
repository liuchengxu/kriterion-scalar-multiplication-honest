import Proof.Privacy.Simulator.Arithmetic.SamplerPlan

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
open Security.SimulatorSampling

/-- A fixed schedule stores each source draw in one word. -/
structure PrivateSchedule {A : Type} {count : Nat} (source : Code A count) where
  plan : List DrawSpec
  words : A → List Word
  planLength : plan.length = count
  wordsLength : ∀ value, (words value).length = count
  sourceLaw : ∀ [BN254.FieldCertificate] (attempts : Nat),
    drawPlanLaw attempts plan = (source.total attempts).law.map words

/-- Count casts preserve the fixed schedule. -/
def PrivateSchedule.cast {A : Type} {first second : Nat} {source : Code A first}
    (schedule : PrivateSchedule source) (same : first = second) : PrivateSchedule (source.cast same) := by
  cases same
  exact schedule

/-- An equivalence changes only the typed view of the stored words. -/
def PrivateSchedule.equiv {A B : Type} {count : Nat} {source : Code A count}
    (schedule : PrivateSchedule source) (transform : A ≃ B) : PrivateSchedule (source.map transform) where
  plan := schedule.plan
  words value := schedule.words (transform.symm value)
  planLength := schedule.planLength
  wordsLength value := schedule.wordsLength _
  sourceLaw attempts := drawPlanLaw_map attempts source schedule.plan schedule.words transform
    (fun value => schedule.words (transform.symm value)) (schedule.sourceLaw attempts)
    (by intro value; rw [transform.symm_apply_apply])

/-- A product schedule stores the right source before the left source. -/
def PrivateSchedule.pair {A B : Type} {first second : Nat} {left : Code A first} {right : Code B second}
    (leftSchedule : PrivateSchedule left) (rightSchedule : PrivateSchedule right) :
    PrivateSchedule (left.pair right) where
  plan := rightSchedule.plan ++ leftSchedule.plan
  words := pairWords leftSchedule.words rightSchedule.words
  planLength := by simp [leftSchedule.planLength, rightSchedule.planLength]
  wordsLength value := by simp [pairWords, leftSchedule.wordsLength, rightSchedule.wordsLength]
  sourceLaw attempts := drawPlanLaw_pair attempts left right _ _ _ _
    (leftSchedule.sourceLaw attempts) (rightSchedule.sourceLaw attempts)

/-- Repeated schedules contain exactly the charged number of entries. -/
theorem repeatDrawPlan_length (plan : List DrawSpec) (count : Nat) :
    (repeatDrawPlan plan count).length = count * plan.length := by
  induction count with
  | zero => simp [repeatDrawPlan]
  | succ count ih => simp [repeatDrawPlan, ih, Nat.succ_mul]

/-- A vector schedule stores its source elements in order. -/
def PrivateSchedule.vector {A : Type} {draws : Nat} {source : Code A draws}
    (schedule : PrivateSchedule source) (count : Nat) : PrivateSchedule (source.vector count) where
  plan := repeatDrawPlan schedule.plan count
  words := vectorWords schedule.words
  planLength := by rw [repeatDrawPlan_length, schedule.planLength]
  wordsLength value := by
    unfold vectorWords
    have lengths (values : List A) : (values.flatMap schedule.words).length = values.length * draws := by
      induction values with
      | nil => simp
      | cons head tail ih => simp [ih, schedule.wordsLength, Nat.succ_mul, Nat.add_comm]
    rw [lengths, Vector.length_toList]
  sourceLaw attempts := drawPlanLaw_vector attempts source _ _ (schedule.sourceLaw attempts) count

/-- A primitive source schedule follows its verified word sampler. -/
def PrivateSchedule.primitive {A : Type} (source : Code A 1) (spec : DrawSpec) (encode : A → Word)
    (law : ∀ [BN254.FieldCertificate] (attempts : Nat),
      (totalSamplerMemory spec.1 attempts spec.2 {}).map (fun result => result.1.registers 0) =
        (source.total attempts).law.map encode) : PrivateSchedule source where
  plan := [spec]
  words value := [encode value]
  planLength := rfl
  wordsLength _ := rfl
  sourceLaw attempts := by
    rw [drawPlanLaw_singleton]
    have exactLaw := (totalSamplerMemory_source spec.1 attempts spec.2 {}).symm.trans (law attempts)
    change drawSpecLaw attempts spec = _ at exactLaw
    rw [exactLaw, PMF.map_comp]
    rfl

/-- The field schedule stores one canonical field word. -/
def fieldSchedule : PrivateSchedule field :=
  .primitive field (BitVec.ofNat 256 BN254.baseFieldModulus, 0)
    (fun value => BitVec.ofNat 256 value.val) (fun attempts => fieldSamplerMemory_source attempts {})

/-- The quotient schedule stores one finite hash-lift integer. -/
def quotientSchedule : PrivateSchedule quotient :=
  .primitive quotient (BitVec.ofNat 256 Security.hashLiftQuotientCount, 0)
    (fun value => BitVec.ofNat 256 value.val) (fun attempts => quotientSamplerMemory_source attempts {})

/-- The bit schedule stores each block in the low bits of one word. -/
def bitsSchedule (width : Nat) (fits : width ≤ 256) : PrivateSchedule (bits width) :=
  .primitive (bits width) (BitVec.ofNat 256 (2 ^ width), 0)
    (fun value => value.setWidth 256) (fun attempts => bitsSamplerMemory_source width attempts {} fits)

/-- The scale schedule includes the explicit nonzero fallback. -/
def scaleSchedule : PrivateSchedule scale :=
  .primitive scale (BitVec.ofNat 256 (BN254.baseFieldModulus - 1), 1)
    (fun value => BitVec.ofNat 256 value.value.val) (fun attempts => scaleSamplerMemory_source attempts {})

/-- The table schedule stores its one random row. -/
def tableSchedule : PrivateSchedule table := (bitsSchedule 256 (by decide)).equiv tableEquiv

/-- The gate schedule stores targets, quotients, tables, and coefficients. -/
def gateArraysSchedule (coefficients gates : Nat) : PrivateSchedule (gateArrays coefficients gates) :=
  ((fieldSchedule.vector coefficients).pair
    (((tableSchedule.vector coordinateBitCount).vector gates).pair
      (((quotientSchedule.vector coordinateBitCount).vector gates).pair
        ((fieldSchedule.vector coordinateBitCount).vector gates)))).cast (by ring)

/-- The gate data uses the array schedule without extra random draws. -/
def gateDataSchedule (coefficients gates : Nat) : PrivateSchedule (gateData coefficients gates) :=
  (gateArraysSchedule coefficients gates).equiv (gateArraysEquiv coefficients gates)

/-- The row schedule stores z, y, and x gate data. -/
def rowSchedule : PrivateSchedule row :=
  (((gateDataSchedule 5 4).equiv xEquiv).pair
    (((gateDataSchedule 4 3).equiv yEquiv).pair ((gateDataSchedule 5 5).equiv zEquiv))).equiv rowEquiv

/-- The public schedule stores all rows before the curve data. -/
def publicSchedule : PrivateSchedule publicSample :=
  (((gateDataSchedule 3 5).equiv curveEquiv).pair
    (rowSchedule.vector FieldMacToECMac.outputMacCount)).equiv publicEquiv

/-- The key schedule stores the true label before the false label. -/
def keySchedule : PrivateSchedule key :=
  ((bitsSchedule 128 (by decide)).pair (bitsSchedule 128 (by decide))).equiv keyEquiv

/-- The input key schedule stores y keys before x keys. -/
def inputKeySchedule : PrivateSchedule inputKey :=
  ((keySchedule.vector coordinateBitCount).pair (keySchedule.vector coordinateBitCount)).equiv inputKeyEquiv

/-- The offline schedule stores the bridge key, input key, and public sample. -/
def offlineSchedule : PrivateSchedule offline := publicSchedule.pair (inputKeySchedule.pair fieldSchedule)

/-- The offline schedule has exactly 838208 fixed arithmetic sampling entries. -/
theorem offlineSchedule_length : offlineSchedule.plan.length = 838208 := offlineSchedule.planLength

/-- The offline word layout has the exact total source law, including every fallback. -/
theorem offlineSchedule_source [BN254.FieldCertificate] (attempts : Nat) :
    drawPlanLaw attempts offlineSchedule.plan = (offline.total attempts).law.map offlineSchedule.words :=
  offlineSchedule.sourceLaw attempts

end Kriterion.ArgoMAC.ArithmeticSimulator
