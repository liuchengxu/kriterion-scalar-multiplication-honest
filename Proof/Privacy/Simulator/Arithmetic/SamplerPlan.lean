import Proof.Privacy.Simulator.Arithmetic.PrivateSamplers
import Construction.Simulator.SamplerBatch

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each schedule entry has the exact total-integer word law. -/
noncomputable def drawSpecLaw (attempts : Nat) (spec : DrawSpec) : PMF Word :=
  (Security.BoundedIntegerSampling.totalInteger (runtimeRange spec.1) (runtimeRange_bounds spec.1).1 attempts).law.map
    (fun value => BitVec.ofNat 256 value.val + spec.2)

/-- A fixed schedule lists its sampled words in execution order. -/
noncomputable def drawPlanLaw (attempts : Nat) : List DrawSpec → PMF (List Word)
  | [] => PMF.pure []
  | spec :: rest => (drawSpecLaw attempts spec).bind fun word =>
      (drawPlanLaw attempts rest).map (List.cons word)

/-- Adjacent schedules concatenate their sampled word lists. -/
theorem drawPlanLaw_append (attempts : Nat) (first second : List DrawSpec) :
    drawPlanLaw attempts (first ++ second) = (drawPlanLaw attempts first).bind fun left =>
      (drawPlanLaw attempts second).map fun right => left ++ right := by
  induction first with
  | nil =>
      simp only [List.nil_append, drawPlanLaw, PMF.pure_bind]
      exact (PMF.map_id _).symm
  | cons spec rest ih =>
      simp only [List.cons_append, drawPlanLaw, ih, PMF.bind_bind, PMF.map_bind,
        PMF.bind_map, PMF.map_comp, Function.comp_def, List.cons_append]

/-- A singleton schedule returns one word. -/
theorem drawPlanLaw_singleton (attempts : Nat) (spec : DrawSpec) :
    drawPlanLaw attempts [spec] = (drawSpecLaw attempts spec).map List.singleton := by
  simp only [drawPlanLaw, PMF.map, PMF.pure_bind]
  rfl

/-- Each source pair samples its right part before its left part. -/
def pairWords {A B : Type} (left : A → List Word) (right : B → List Word) (value : A × B) : List Word :=
  right value.2 ++ left value.1

/-- Vector words retain the source element order. -/
def vectorWords {A : Type} {count : Nat} (encode : A → List Word) (value : Vector A count) : List Word :=
  value.toList.flatMap encode

/-- Repeated schedules preserve the source vector order. -/
def repeatDrawPlan (plan : List DrawSpec) : Nat → List DrawSpec
  | 0 => []
  | count + 1 => repeatDrawPlan plan count ++ plan

/-- Count casts preserve the total source law. -/
theorem totalCode_cast_law {A : Type} {first second : Nat} (same : first = second)
    (source : Security.SimulatorSampling.Code A first) (attempts : Nat) :
    ((source.cast same).total attempts).law = (source.total attempts).law := by
  cases same
  rfl

/-- A source map preserves the schedule when its word representation agrees. -/
theorem drawPlanLaw_map {A B : Type} {count : Nat} (attempts : Nat)
    (source : Security.SimulatorSampling.Code A count) (plan : List DrawSpec)
    (encode : A → List Word) (transform : A → B) (result : B → List Word)
    (law : drawPlanLaw attempts plan = (source.total attempts).law.map encode)
    (agrees : ∀ value, result (transform value) = encode value) :
    drawPlanLaw attempts plan = ((source.map transform).total attempts).law.map result := by
  rw [totalCode_map_law, PMF.map_comp]
  simpa only [Function.comp_def, agrees] using law

/-- Product schedules follow the exact right-before-left source order. -/
theorem drawPlanLaw_pair {A B : Type} {first second : Nat} (attempts : Nat)
    (left : Security.SimulatorSampling.Code A first) (right : Security.SimulatorSampling.Code B second)
    (leftPlan rightPlan : List DrawSpec) (leftWords : A → List Word) (rightWords : B → List Word)
    (leftLaw : drawPlanLaw attempts leftPlan = (left.total attempts).law.map leftWords)
    (rightLaw : drawPlanLaw attempts rightPlan = (right.total attempts).law.map rightWords) :
    drawPlanLaw attempts (rightPlan ++ leftPlan) =
      ((left.pair right).total attempts).law.map (pairWords leftWords rightWords) := by
  rw [drawPlanLaw_append, rightLaw]
  simp only [PMF.bind_map, leftLaw, PMF.map_comp, Function.comp_def,
    Security.SimulatorSampling.Code.pair, Security.SimulatorSampling.Code.total,
    Security.BoundedIntegerSampling.BitCode.bind_law, totalCode_map_law, PMF.map_bind, pairWords]

/-- Vector schedules retain the complete total source law. -/
theorem drawPlanLaw_vector {A : Type} {draws : Nat} (attempts : Nat)
    (source : Security.SimulatorSampling.Code A draws) (plan : List DrawSpec) (encode : A → List Word)
    (law : drawPlanLaw attempts plan = (source.total attempts).law.map encode) (count : Nat) :
    drawPlanLaw attempts (repeatDrawPlan plan count) =
      ((source.vector count).total attempts).law.map (vectorWords encode) := by
  induction count with
  | zero =>
      simp only [repeatDrawPlan, drawPlanLaw, Security.SimulatorSampling.Code.vector, totalCode_cast_law,
        Security.SimulatorSampling.Code.total, Security.BoundedIntegerSampling.BitCode.law, PMF.pure_map]
      rfl
  | succ count ih =>
      rw [Security.SimulatorSampling.Code.vector, totalCode_cast_law]
      apply drawPlanLaw_map attempts (source.pair (source.vector count)) _ _
        (Security.SimulatorSampling.vectorPushEquiv A count) (vectorWords encode)
        (drawPlanLaw_pair attempts source (source.vector count) plan (repeatDrawPlan plan count)
          encode (vectorWords encode) law ih)
      intro value
      simp [vectorWords, pairWords, Security.SimulatorSampling.vectorPushEquiv, Vector.toList_push]

end Kriterion.ArgoMAC.ArithmeticSimulator
