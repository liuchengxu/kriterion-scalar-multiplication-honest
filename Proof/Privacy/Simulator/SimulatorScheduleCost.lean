/-
This file counts deterministic simulator work on explicit finite arrays.
One primitive step is one group operation, one fixed-width field or word operation,
or one array or list read or write.
The counter includes conservative allowances for fixed record fields and closure captures.
The counter does not specify a compiler or a Turing machine.
The counter excludes the bookkeeping that records the count.
-/

import Proof.Privacy.Simulator.SimulatorRetargetCost
import Proof.Privacy.Simulator.SimulatorSampling

namespace Kriterion.ArgoMAC.Security.SimulatorScheduleCost

open BN254 Cryptography SimulatorRetargetCost

/-- This view supplies an explicit array for one indexed input table. -/
structure TableView {Value : Type} {count : Nat} (source : Fin count → Value) where
  data : Vector Value count
  get_eq : data.get = source

/-- The array itself supplies its getter view without evaluating another function. -/
def TableView.ofVector {Value : Type} {count : Nat} (data : Vector Value count) :
    TableView data.get := ⟨data, rfl⟩

private theorem vector_toList {Value : Type} {count : Nat} (values : Vector Value count) :
    values.toList = List.ofFn values.get := by
  have same : values = Vector.ofFn values.get := by
    apply Vector.ext
    intro index valid
    simp
    rfl
  conv_lhs => rw [same]
  exact Vector.toList_ofFn

private theorem vector_get_ofFn {Value : Type} {count : Nat} (values : Fin count → Value) :
    (Vector.ofFn values).get = values := by
  funext index
  exact Vector.get_ofFn values index

/-- This fold includes the array-to-list read and write operations. -/
def arrayBitsWithCost {count : Nat} (values : Vector BaseField count) : BaseField × Nat :=
  let result := fromBitsWithCost values.toList
  (result.1, result.2.fieldAdditions + result.2.fieldMultiplications +
    result.2.elements + 2 * count)

theorem arrayBitsWithCost_value {count : Nat} (values : Vector BaseField count) :
    (arrayBitsWithCost values).1 = DigitAdaptor.fromBits values.get := by
  simp only [arrayBitsWithCost]
  rw [vector_toList, fromBitsWithCost_value]

theorem arrayBitsWithCost_count {count : Nat} (values : Vector BaseField count) :
    (arrayBitsWithCost values).2 = 5 * count := by
  obtain ⟨adds, muls, reads, _, _, _⟩ := fromBitsWithCost_bound values.toList
  simp only [Vector.length_toList] at adds muls reads
  simp only [arrayBitsWithCost, adds, muls, reads]
  omega

/-- This syntax permits only field primitives and explicit table folds. -/
inductive FieldExpr where
  | input (value : BaseField)
  | bits {count : Nat} (values : Vector BaseField count)
  | add (left right : FieldExpr)
  | sub (left right : FieldExpr)
  | mul (left right : FieldExpr)

/-- This interpreter counts every primitive operation in the expression. -/
def FieldExpr.run : FieldExpr → BaseField × Nat
  | .input value => (value, 1)
  | .bits values => arrayBitsWithCost values
  | .add left right =>
      let a := left.run
      let b := right.run
      (a.1 + b.1, a.2 + b.2 + 1)
  | .sub left right =>
      let a := left.run
      let b := right.run
      (a.1 - b.1, a.2 + b.2 + 1)
  | .mul left right =>
      let a := left.run
      let b := right.run
      (a.1 * b.1, a.2 + b.2 + 1)

/-- This structural count includes the full cost of every table fold. -/
def FieldExpr.work : FieldExpr → Nat
  | .input _ => 1
  | .bits (count := count) _ => 5 * count
  | .add left right | .sub left right | .mul left right => left.work + right.work + 1

theorem FieldExpr.run_work (expression : FieldExpr) : expression.run.2 = expression.work := by
  induction expression with
  | input value => rfl
  | bits values => exact arrayBitsWithCost_count values
  | add left right ihLeft ihRight | sub left right ihLeft ihRight | mul left right ihLeft ihRight =>
      simp only [run, work, ihLeft, ihRight]

/-- This expression expands every operation in the curve request result. -/
def curveResultExpr (request : CurveGateRequest) (input : AffineInput)
    (x3 : TableView request.x3Targets)
    (x5 : TableView request.x5Targets)
    (x7 : TableView request.x7Targets)
    (y4 : TableView request.y4Targets)
    (y6 : TableView request.y6Targets) : FieldExpr :=
  (.add (.add (.add (.add (.add (.add (.add (.input request.c0) (.mul (.input request.c1) (.mul (.mul (.input input.x) (.input input.x)) (.input input.x)))) (.mul (.input request.c2) (.mul (.input input.y) (.input input.y)))) (.mul (.bits x3.data) (.mul (.input input.x) (.input input.x)))) (.mul (.bits y4.data) (.input input.y))) (.mul (.bits x5.data) (.input input.x))) (.bits y6.data)) (.bits x7.data))

theorem curveResultExpr_value (request : CurveGateRequest) (input : AffineInput)
    (x3 : TableView request.x3Targets)
    (x5 : TableView request.x5Targets)
    (x7 : TableView request.x7Targets)
    (y4 : TableView request.y4Targets)
    (y6 : TableView request.y6Targets) :
    (curveResultExpr request input x3 x5 x7 y4 y6).run.1 = request.result input := by
  simp only [curveResultExpr, FieldExpr.run, arrayBitsWithCost_value,
    x3.get_eq, x5.get_eq, x7.get_eq, y4.get_eq, y6.get_eq, CurveGateRequest.result, pow_succ, pow_zero, one_mul]

theorem curveResultExpr_bound (request : CurveGateRequest) (input : AffineInput)
    (x3 : TableView request.x3Targets)
    (x5 : TableView request.x5Targets)
    (x7 : TableView request.x7Targets)
    (y4 : TableView request.y4Targets)
    (y6 : TableView request.y6Targets) :
    (curveResultExpr request input x3 x5 x7 y4 y6).run.2 ≤ 6500 := by
  rw [FieldExpr.run_work]
  simp only [curveResultExpr, FieldExpr.work, coordinateBitCount]
  decide

/-- This expression expands every operation in the x request result. -/
def xResultExpr (request : BiquadraticXRequest) (input : AffineInput)
    (y6 : TableView request.y6Targets)
    (y8 : TableView request.y8Targets)
    (y10 : TableView request.y10Targets)
    (x9 : TableView request.x9Targets) : FieldExpr :=
  (.add (.add (.add (.add (.add (.add (.add (.add (.input request.c0) (.mul (.input request.c1) (.input input.x))) (.mul (.input request.c2) (.input input.y))) (.mul (.mul (.input request.c3) (.input input.x)) (.input input.y))) (.mul (.input request.c5) (.mul (.input input.y) (.input input.y)))) (.mul (.bits y6.data) (.input input.x))) (.mul (.bits y8.data) (.input input.y))) (.bits x9.data)) (.bits y10.data))

theorem xResultExpr_value (request : BiquadraticXRequest) (input : AffineInput)
    (y6 : TableView request.y6Targets)
    (y8 : TableView request.y8Targets)
    (y10 : TableView request.y10Targets)
    (x9 : TableView request.x9Targets) :
    (xResultExpr request input y6 y8 y10 x9).run.1 = request.result input := by
  simp only [xResultExpr, FieldExpr.run, arrayBitsWithCost_value,
    y6.get_eq, y8.get_eq, y10.get_eq, x9.get_eq, BiquadraticXRequest.result, pow_succ, pow_zero, one_mul]

theorem xResultExpr_bound (request : BiquadraticXRequest) (input : AffineInput)
    (y6 : TableView request.y6Targets)
    (y8 : TableView request.y8Targets)
    (y10 : TableView request.y10Targets)
    (x9 : TableView request.x9Targets) :
    (xResultExpr request input y6 y8 y10 x9).run.2 ≤ 5200 := by
  rw [FieldExpr.run_work]
  simp only [xResultExpr, FieldExpr.work, coordinateBitCount]
  decide

/-- This expression expands every operation in the y request result. -/
def yResultExpr (request : BiquadraticYRequest) (input : AffineInput)
    (y6 : TableView request.y6Targets)
    (x7 : TableView request.x7Targets)
    (x9 : TableView request.x9Targets) : FieldExpr :=
  (.add (.add (.add (.add (.add (.add (.input request.c0) (.mul (.input request.c1) (.input input.x))) (.mul (.input request.c4) (.mul (.input input.x) (.input input.x)))) (.mul (.input request.c5) (.mul (.mul (.input input.x) (.input input.x)) (.input input.x)))) (.mul (.bits y6.data) (.mul (.input input.x) (.input input.x)))) (.mul (.bits x7.data) (.input input.x))) (.bits x9.data))

theorem yResultExpr_value (request : BiquadraticYRequest) (input : AffineInput)
    (y6 : TableView request.y6Targets)
    (x7 : TableView request.x7Targets)
    (x9 : TableView request.x9Targets) :
    (yResultExpr request input y6 x7 x9).run.1 = request.result input := by
  simp only [yResultExpr, FieldExpr.run, arrayBitsWithCost_value,
    y6.get_eq, x7.get_eq, x9.get_eq, BiquadraticYRequest.result, pow_succ, pow_zero, one_mul]

theorem yResultExpr_bound (request : BiquadraticYRequest) (input : AffineInput)
    (y6 : TableView request.y6Targets)
    (x7 : TableView request.x7Targets)
    (x9 : TableView request.x9Targets) :
    (yResultExpr request input y6 x7 x9).run.2 ≤ 5200 := by
  rw [FieldExpr.run_work]
  simp only [yResultExpr, FieldExpr.work, coordinateBitCount]
  decide

/-- This expression expands every operation in the z request result. -/
def zResultExpr (request : BiquadraticZRequest) (input : AffineInput)
    (y6 : TableView request.y6Targets)
    (y8 : TableView request.y8Targets)
    (y10 : TableView request.y10Targets)
    (x7 : TableView request.x7Targets)
    (x9 : TableView request.x9Targets) : FieldExpr :=
  (.add (.add (.add (.add (.add (.add (.add (.add (.add (.input request.c0) (.mul (.input request.c2) (.input input.y))) (.mul (.mul (.input request.c3) (.input input.x)) (.input input.y))) (.mul (.input request.c4) (.mul (.input input.x) (.input input.x)))) (.mul (.input request.c5) (.mul (.input input.y) (.input input.y)))) (.mul (.bits y6.data) (.input input.x))) (.mul (.bits x7.data) (.input input.x))) (.mul (.bits y8.data) (.input input.y))) (.bits x9.data)) (.bits y10.data))

theorem zResultExpr_value (request : BiquadraticZRequest) (input : AffineInput)
    (y6 : TableView request.y6Targets)
    (y8 : TableView request.y8Targets)
    (y10 : TableView request.y10Targets)
    (x7 : TableView request.x7Targets)
    (x9 : TableView request.x9Targets) :
    (zResultExpr request input y6 y8 y10 x7 x9).run.1 = request.result input := by
  simp only [zResultExpr, FieldExpr.run, arrayBitsWithCost_value,
    y6.get_eq, y8.get_eq, y10.get_eq, x7.get_eq, x9.get_eq, BiquadraticZRequest.result, pow_succ, pow_zero, one_mul]

theorem zResultExpr_bound (request : BiquadraticZRequest) (input : AffineInput)
    (y6 : TableView request.y6Targets)
    (y8 : TableView request.y8Targets)
    (y10 : TableView request.y10Targets)
    (x7 : TableView request.x7Targets)
    (x9 : TableView request.x9Targets) :
    (zResultExpr request input y6 y8 y10 x7 x9).run.2 ≤ 6500 := by
  rw [FieldExpr.run_work]
  simp only [zResultExpr, FieldExpr.work, coordinateBitCount]
  decide

/-- This vector wrapper preserves the counted low-target computation. -/
def retargetVectorWithCost {count : Nat} (values : Vector BaseField (count + 1))
    (target : BaseField) : Vector BaseField (count + 1) × Nat :=
  let result := retargetBitsWithCost values target
  (⟨result.1, by rw [retargetBitsWithCost_value]; exact (Vector.ofFn _).size_toArray⟩,
    result.2.fieldAdditions + result.2.fieldMultiplications + result.2.elements)

theorem retargetVectorWithCost_value {count : Nat} (values : Vector BaseField (count + 1))
    (target : BaseField) :
    (retargetVectorWithCost values target).1 = Vector.ofFn (retargetBits values.get target) := by
  apply Vector.toArray_inj.mp
  exact retargetBitsWithCost_value values target

theorem retargetVectorWithCost_count {count : Nat} (values : Vector BaseField (count + 1))
    (target : BaseField) : (retargetVectorWithCost values target).2 = 7 * count + 8 := by
  obtain ⟨adds, muls, reads, _, _, _⟩ := retargetBitsWithCost_bound values target
  simp only [retargetVectorWithCost, adds, muls, reads]
  omega

/-- This computation uses one word multiplication, one word sum, and one truncation. -/
def goodLiftWithCost (target : BaseField) (quotient : HashLiftQuotient) : BitVec 384 × Nat :=
  (BitVec.ofNat 384 (target.val + baseFieldModulus * quotient.val), 3)

theorem goodLiftWithCost_value (target : BaseField) (quotient : HashLiftQuotient) :
    (goodLiftWithCost target quotient).1 = (goodHashLift target quotient).1 := rfl

/-- This array stores all lift bytes before the schedule reads them. -/
structure LiftArray {count : Nat} (targets : Vector BaseField count) where
  data : Vector (BitVec 384) count
  represents : ∀ index, HashLiftRepresents (data.get index) (targets.get index)

def LiftArray.get {count : Nat} {targets : Vector BaseField count}
    (lifts : LiftArray targets) (index : Fin count) : HashLift (targets.get index) :=
  ⟨lifts.data.get index, lifts.represents index⟩

/-- The tabulation counts two input reads and one row write in each callback. -/
def makeLiftsWithCost {count : Nat} (targets : Vector BaseField count)
    (quotients : Vector HashLiftQuotient count) : LiftArray targets × Nat :=
  let rows := Vector.ofFn (fun index =>
    let result := goodLiftWithCost (targets.get index) (quotients.get index)
    (result.1, result.2 + 3))
  (⟨rows.map Prod.fst, by
      intro index
      dsimp only [rows]
      simpa only [Vector.get_map, Vector.get_ofFn, goodLiftWithCost_value] using
        (goodHashLift (targets.get index) (quotients.get index)).property⟩,
    (rows.toList.map Prod.snd).sum + 2 * count)

theorem makeLiftsWithCost_get {count : Nat} (targets : Vector BaseField count)
    (quotients : Vector HashLiftQuotient count) (index : Fin count) :
    ((makeLiftsWithCost targets quotients).1.get index).1 =
      (goodHashLift (targets.get index) (quotients.get index)).1 := by
  simp only [makeLiftsWithCost, LiftArray.get, Vector.get_map, Vector.get_ofFn,
    goodLiftWithCost_value]

theorem makeLiftsWithCost_count {count : Nat} (targets : Vector BaseField count)
    (quotients : Vector HashLiftQuotient count) :
    (makeLiftsWithCost targets quotients).2 = 8 * count := by
  simp only [makeLiftsWithCost, goodLiftWithCost, Vector.toList_ofFn, List.map_ofFn]
  simp [Function.comp_def, List.ofFn_const]
  omega

theorem makeLiftsWithCost_get_eq {count : Nat} (targets : Vector BaseField count)
    (quotients : Vector HashLiftQuotient count) (index : Fin count) :
    (makeLiftsWithCost targets quotients).1.get index =
      goodHashLift (targets.get index) (quotients.get index) := by
  apply Subtype.ext
  exact makeLiftsWithCost_get targets quotients index

private theorem makeLiftsWithCost_get_fun {count : Nat} (targets : Vector BaseField count)
    (quotients : Vector HashLiftQuotient count) :
    (makeLiftsWithCost targets quotients).1.get =
      (fun index => goodHashLift (targets.get index) (quotients.get index)) := by
  funext index
  exact makeLiftsWithCost_get_eq targets quotients index

/-- This value stores the materialized targets and their materialized lifts. -/
structure RetargetData (count : Nat) where
  targets : Vector BaseField count
  lifts : LiftArray targets
  work : Nat

/-- This computation executes the residual arithmetic, target update, and lift construction. -/
def retargetDataWithCost (old : Vector BaseField coordinateBitCount)
    (quotients : Vector HashLiftQuotient coordinateBitCount) (target : BaseField)
    (result : FieldExpr) : RetargetData coordinateBitCount :=
  let residual := (FieldExpr.add (.sub (.input target) result) (.bits old)).run
  let values := retargetVectorWithCost (count := 253) old residual.1
  let lifts := makeLiftsWithCost values.1 quotients
  ⟨values.1, lifts.1, residual.2 + values.2 + lifts.2⟩

theorem retargetDataWithCost_bound (old : Vector BaseField coordinateBitCount)
    (quotients : Vector HashLiftQuotient coordinateBitCount) (target : BaseField)
    (result : FieldExpr) :
    (retargetDataWithCost old quotients target result).work = result.work + 5084 := by
  simp only [retargetDataWithCost, FieldExpr.run_work, FieldExpr.work,
    retargetVectorWithCost_count, makeLiftsWithCost_count, coordinateBitCount]
  omega

/-- This wrapper preserves the output-array cost and its exact vector size. -/
def outputTargetsVectorWithCost [FieldCertificate] [GroupCertificate]
    (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) :
    Vector FieldMacToECMac.HomogeneousValue FieldMacToECMac.outputMacCount × Nat :=
  let result := outputTargetsWithCost point free scales
  (⟨result.1, by rw [outputTargetsWithCost_value]; exact (outputTargets point free scales.get).size_toArray⟩,
    result.2.groupAdditions + result.2.groupNegations + result.2.fieldAdditions +
      result.2.fieldMultiplications + result.2.fieldDivisions + result.2.elements +
      result.2.scalarOperations)

theorem outputTargetsVectorWithCost_value [FieldCertificate] [GroupCertificate]
    (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) :
    (outputTargetsVectorWithCost point free scales).1 = outputTargets point free scales.get := by
  apply Vector.toArray_inj.mp
  exact outputTargetsWithCost_value point free scales

theorem outputTargetsVectorWithCost_bound [FieldCertificate] [GroupCertificate]
    (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) :
    (outputTargetsVectorWithCost point free scales).2 ≤ 141403 := by
  obtain ⟨ga, gn, fa, fm, fd, elements⟩ := outputTargetsWithCost_bound point free scales
  have scalar := outputTargetsWithCost_scalarOperations point free scales
  simp only [outputTargetsVectorWithCost]
  omega

/-- These arrays supply a gate target and its canonical lift quotient. -/
structure GateInputs {count : Nat} (targetSource : Fin count → BaseField)
    (quotientSource : Fin count → HashLiftQuotient) (lifts : ∀ index, HashLift (targetSource index)) where
  targets : TableView targetSource
  quotients : TableView quotientSource
  canonical : ∀ index, lifts index = goodHashLift (targetSource index) (quotientSource index)

/-- This typed wrapper keeps the same three word operations. -/
def typedLiftWithCost (target : BaseField) (quotient : HashLiftQuotient) : HashLift target × Nat :=
  let result := goodLiftWithCost target quotient
  (⟨result.1, by rw [goodLiftWithCost_value]; exact (goodHashLift target quotient).property⟩,
    result.2)

private theorem typedLiftWithCost_value (target : BaseField) (quotient : HashLiftQuotient) :
    (typedLiftWithCost target quotient).1 = goodHashLift target quotient := by
  apply Subtype.ext
  exact goodLiftWithCost_value target quotient

/-- The callback counts four array reads, coordinate-bit operations, and record writes. -/
def digitScheduleWithCost
    (location : Pipeline.FixedKeyLocation) (tables : Vector BitAdaptor.Table coordinateBitCount)
    (coordinate : BaseField) (labels : Vector Block coordinateBitCount)
    {targets : Fin coordinateBitCount → BaseField}
    {quotients : Fin coordinateBitCount → HashLiftQuotient}
    {lifts : ∀ index, HashLift (targets index)} (inputs : GateInputs targets quotients lifts) :
    List GateDirective × Nat :=
  let rows := List.ofFn (fun index : Fin coordinateBitCount =>
    let target := inputs.targets.data.get index
    let quotient := inputs.quotients.data.get index
    let lift := typedLiftWithCost target quotient
    let directive : GateDirective := {
      location, window := index.val, bit := coordinateValues coordinate index,
      label := labels.get index, table := tables.get index, target, lift := lift.1 }
    (directive, lift.2 + 16))
  (rows.map Prod.fst, (rows.map Prod.snd).sum + 2 * coordinateBitCount)

theorem digitScheduleWithCost_value
    (location : Pipeline.FixedKeyLocation) (tables : Vector BitAdaptor.Table coordinateBitCount)
    (coordinate : BaseField) (labels : Vector Block coordinateBitCount)
    {targets : Fin coordinateBitCount → BaseField}
    {quotients : Fin coordinateBitCount → HashLiftQuotient}
    {lifts : ∀ index, HashLift (targets index)} (inputs : GateInputs targets quotients lifts) :
    (digitScheduleWithCost location tables coordinate labels inputs).1 =
      digitGateSchedule location tables (coordinateValues coordinate) labels targets lifts := by
  simp only [digitScheduleWithCost, List.map_ofFn, Function.comp_def, typedLiftWithCost_value]
  rw [inputs.targets.get_eq, inputs.quotients.get_eq]
  simp only [digitGateSchedule, inputs.canonical]

theorem digitScheduleWithCost_count
    (location : Pipeline.FixedKeyLocation) (tables : Vector BitAdaptor.Table coordinateBitCount)
    (coordinate : BaseField) (labels : Vector Block coordinateBitCount)
    {targets : Fin coordinateBitCount → BaseField}
    {quotients : Fin coordinateBitCount → HashLiftQuotient}
    {lifts : ∀ index, HashLift (targets index)} (inputs : GateInputs targets quotients lifts) :
    (digitScheduleWithCost location tables coordinate labels inputs).2 = 5334 := by
  simp only [digitScheduleWithCost, typedLiftWithCost, goodLiftWithCost, List.map_ofFn,
    Function.comp_def]
  rw [List.ofFn_const]
  norm_num [coordinateBitCount]

/-- This traversal counts each list copy and each chunk read. -/
def flattenWithCost : List (List GateDirective × Nat) → List GateDirective × Nat
  | [] => ([], 0)
  | chunk :: chunks =>
      let tail := flattenWithCost chunks
      (chunk.1 ++ tail.1, chunk.2 + tail.2 + 2 * chunk.1.length + 2)

theorem flattenWithCost_value (chunks : List (List GateDirective × Nat)) :
    (flattenWithCost chunks).1 = (chunks.map Prod.fst).flatten := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih => simp [flattenWithCost, ih]

theorem flattenWithCost_count (chunks : List (List GateDirective × Nat)) :
    (flattenWithCost chunks).2 =
      (chunks.map Prod.snd).sum + 2 * ((chunks.map Prod.fst).map List.length).sum +
        2 * chunks.length := by
  induction chunks with
  | nil => simp [flattenWithCost]
  | cons chunk chunks ih =>
      simp only [flattenWithCost, List.map_cons, List.sum_cons, List.length_cons, ih]
      omega

/-- These arrays supply every gate in the curve schedule. -/
structure CurveScheduleTables (request : CurveGateRequest) where
  x3 : GateInputs request.x3Targets request.x3Quotients request.x3Lifts
  x5 : GateInputs request.x5Targets request.x5Quotients request.x5Lifts
  x7 : GateInputs request.x7Targets request.x7Quotients request.x7Lifts
  y4 : GateInputs request.y4Targets request.y4Quotients request.y4Lifts
  y6 : GateInputs request.y6Targets request.y6Quotients request.y6Lifts

def curveScheduleWithCost (request : CurveGateRequest)
    (input : AffineInput) (inputMac : InputMac) (tables : CurveScheduleTables request) :
    List GateDirective × Nat :=
  flattenWithCost [
    digitScheduleWithCost (.curve .x3) request.x3Table input.x inputMac.x tables.x3, digitScheduleWithCost (.curve .x5) request.x5Table input.x inputMac.x tables.x5, digitScheduleWithCost (.curve .x7) request.x7Table input.x inputMac.x tables.x7, digitScheduleWithCost (.curve .y4) request.y4Table input.y inputMac.y tables.y4, digitScheduleWithCost (.curve .y6) request.y6Table input.y inputMac.y tables.y6]

theorem curveScheduleWithCost_value (request : CurveGateRequest)
    (input : AffineInput) (inputMac : InputMac) (tables : CurveScheduleTables request) :
    (curveScheduleWithCost request input inputMac tables).1 =
      request.schedule input inputMac := by
  simp only [curveScheduleWithCost, flattenWithCost_value, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, digitScheduleWithCost_value, List.append_nil,
    CurveGateRequest.schedule, List.append_assoc]

theorem curveScheduleWithCost_count (request : CurveGateRequest)
    (input : AffineInput) (inputMac : InputMac) (tables : CurveScheduleTables request) :
    (curveScheduleWithCost request input inputMac tables).2 = 29220 := by
  simp only [curveScheduleWithCost, flattenWithCost_count, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    digitScheduleWithCost_count, digitScheduleWithCost_value, digitGateSchedule_length,
    coordinateBitCount]
  norm_num

/-- These arrays supply every gate in the x schedule. -/
structure XScheduleTables (request : BiquadraticXRequest) where
  y6 : GateInputs request.y6Targets request.y6Quotients request.y6Lifts
  y8 : GateInputs request.y8Targets request.y8Quotients request.y8Lifts
  y10 : GateInputs request.y10Targets request.y10Quotients request.y10Lifts
  x9 : GateInputs request.x9Targets request.x9Quotients request.x9Lifts

def xScheduleWithCost (request : BiquadraticXRequest) (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) (tables : XScheduleTables request) :
    List GateDirective × Nat :=
  flattenWithCost [
    digitScheduleWithCost (.point output .x .y6) request.y6Table input.y inputMac.y tables.y6, digitScheduleWithCost (.point output .x .y8) request.y8Table input.y inputMac.y tables.y8, digitScheduleWithCost (.point output .x .y10) request.y10Table input.y inputMac.y tables.y10, digitScheduleWithCost (.point output .x .x9) request.x9Table input.x inputMac.x tables.x9]

theorem xScheduleWithCost_value (request : BiquadraticXRequest) (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) (tables : XScheduleTables request) :
    (xScheduleWithCost request output input inputMac tables).1 =
      request.schedule output input inputMac := by
  simp only [xScheduleWithCost, flattenWithCost_value, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, digitScheduleWithCost_value, List.append_nil,
    BiquadraticXRequest.schedule, biquadraticXGateSchedule, List.append_assoc]

theorem xScheduleWithCost_count (request : BiquadraticXRequest) (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) (tables : XScheduleTables request) :
    (xScheduleWithCost request output input inputMac tables).2 = 23376 := by
  simp only [xScheduleWithCost, flattenWithCost_count, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    digitScheduleWithCost_count, digitScheduleWithCost_value, digitGateSchedule_length,
    coordinateBitCount]
  norm_num

/-- These arrays supply every gate in the y schedule. -/
structure YScheduleTables (request : BiquadraticYRequest) where
  y6 : GateInputs request.y6Targets request.y6Quotients request.y6Lifts
  x7 : GateInputs request.x7Targets request.x7Quotients request.x7Lifts
  x9 : GateInputs request.x9Targets request.x9Quotients request.x9Lifts

def yScheduleWithCost (request : BiquadraticYRequest) (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) (tables : YScheduleTables request) :
    List GateDirective × Nat :=
  flattenWithCost [
    digitScheduleWithCost (.point output .y .y6) request.y6Table input.x inputMac.x tables.y6, digitScheduleWithCost (.point output .y .x7) request.x7Table input.x inputMac.x tables.x7, digitScheduleWithCost (.point output .y .x9) request.x9Table input.x inputMac.x tables.x9]

theorem yScheduleWithCost_value (request : BiquadraticYRequest) (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) (tables : YScheduleTables request) :
    (yScheduleWithCost request output input inputMac tables).1 =
      request.schedule output input inputMac := by
  simp only [yScheduleWithCost, flattenWithCost_value, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, digitScheduleWithCost_value, List.append_nil,
    BiquadraticYRequest.schedule, biquadraticYGateSchedule, List.append_assoc]

theorem yScheduleWithCost_count (request : BiquadraticYRequest) (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) (tables : YScheduleTables request) :
    (yScheduleWithCost request output input inputMac tables).2 = 17532 := by
  simp only [yScheduleWithCost, flattenWithCost_count, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    digitScheduleWithCost_count, digitScheduleWithCost_value, digitGateSchedule_length,
    coordinateBitCount]
  norm_num

/-- These arrays supply every gate in the z schedule. -/
structure ZScheduleTables (request : BiquadraticZRequest) where
  y6 : GateInputs request.y6Targets request.y6Quotients request.y6Lifts
  y8 : GateInputs request.y8Targets request.y8Quotients request.y8Lifts
  y10 : GateInputs request.y10Targets request.y10Quotients request.y10Lifts
  x7 : GateInputs request.x7Targets request.x7Quotients request.x7Lifts
  x9 : GateInputs request.x9Targets request.x9Quotients request.x9Lifts

def zScheduleWithCost (request : BiquadraticZRequest) (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) (tables : ZScheduleTables request) :
    List GateDirective × Nat :=
  flattenWithCost [
    digitScheduleWithCost (.point output .z .y6) request.y6Table input.y inputMac.y tables.y6, digitScheduleWithCost (.point output .z .y8) request.y8Table input.y inputMac.y tables.y8, digitScheduleWithCost (.point output .z .y10) request.y10Table input.y inputMac.y tables.y10, digitScheduleWithCost (.point output .z .x7) request.x7Table input.x inputMac.x tables.x7, digitScheduleWithCost (.point output .z .x9) request.x9Table input.x inputMac.x tables.x9]

theorem zScheduleWithCost_value (request : BiquadraticZRequest) (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) (tables : ZScheduleTables request) :
    (zScheduleWithCost request output input inputMac tables).1 =
      request.schedule output input inputMac := by
  simp only [zScheduleWithCost, flattenWithCost_value, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, digitScheduleWithCost_value, List.append_nil,
    BiquadraticZRequest.schedule, biquadraticZGateSchedule, List.append_assoc]

theorem zScheduleWithCost_count (request : BiquadraticZRequest) (output : Fin FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) (tables : ZScheduleTables request) :
    (zScheduleWithCost request output input inputMac tables).2 = 29220 := by
  simp only [zScheduleWithCost, flattenWithCost_count, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    digitScheduleWithCost_count, digitScheduleWithCost_value, digitGateSchedule_length,
    coordinateBitCount]
  norm_num

/-- These arrays supply every gate in one point-row schedule. -/
structure RowScheduleTables (request : BiquadraticRowRequest) where
  x : XScheduleTables request.x
  y : YScheduleTables request.y
  z : ZScheduleTables request.z

def rowScheduleWithCost (request : BiquadraticRowRequest)
    (output : Fin FieldMacToECMac.outputMacCount) (input : AffineInput) (inputMac : InputMac)
    (tables : RowScheduleTables request) : List GateDirective × Nat :=
  flattenWithCost [xScheduleWithCost request.x output input inputMac tables.x,
    yScheduleWithCost request.y output input inputMac tables.y,
    zScheduleWithCost request.z output input inputMac tables.z]

theorem rowScheduleWithCost_value (request : BiquadraticRowRequest)
    (output : Fin FieldMacToECMac.outputMacCount) (input : AffineInput) (inputMac : InputMac)
    (tables : RowScheduleTables request) :
    (rowScheduleWithCost request output input inputMac tables).1 =
      request.schedule output input inputMac := by
  simp only [rowScheduleWithCost, flattenWithCost_value, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, xScheduleWithCost_value, yScheduleWithCost_value,
    zScheduleWithCost_value, List.append_nil, BiquadraticRowRequest.schedule,
    biquadraticRowGateSchedule, List.append_assoc]

theorem rowScheduleWithCost_count (request : BiquadraticRowRequest)
    (output : Fin FieldMacToECMac.outputMacCount) (input : AffineInput) (inputMac : InputMac)
    (tables : RowScheduleTables request) :
    (rowScheduleWithCost request output input inputMac tables).2 = 76230 := by
  simp only [rowScheduleWithCost, flattenWithCost_count, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    xScheduleWithCost_count, yScheduleWithCost_count, zScheduleWithCost_count,
    xScheduleWithCost_value, yScheduleWithCost_value, zScheduleWithCost_value,
    BiquadraticXRequest.schedule, BiquadraticYRequest.schedule,
    BiquadraticZRequest.schedule, biquadraticXGateSchedule_length,
    biquadraticYGateSchedule_length, biquadraticZGateSchedule_length, coordinateBitCount]
  norm_num


structure PreparedCurve where
  request : CurveGateRequest
  tables : CurveScheduleTables request

def prepareCurveWithCost (request : CurveGateRequest) (input : AffineInput)
    (target : BaseField) (tables : CurveScheduleTables request) : PreparedCurve × Nat :=
  let data := retargetDataWithCost tables.x7.targets.data tables.x7.quotients.data target
    (curveResultExpr request input tables.x3.targets tables.x5.targets tables.x7.targets tables.y4.targets tables.y6.targets)
  let updated := { request with x7Targets := data.targets.get, x7Lifts := data.lifts.get }
  let views : CurveScheduleTables updated := {
    x3 := tables.x3
    x5 := tables.x5
    x7 := {
      targets := TableView.ofVector data.targets
      quotients := tables.x7.quotients
      canonical := by
        intro index
        change (makeLiftsWithCost _ _).1.get index = _
        rw [makeLiftsWithCost_get_eq, tables.x7.quotients.get_eq] }
    y4 := tables.y4
    y6 := tables.y6
  }
  (⟨updated, views⟩, data.work + 128)

theorem prepareCurveWithCost_value (request : CurveGateRequest) (input : AffineInput)
    (target : BaseField) (tables : CurveScheduleTables request) :
    (prepareCurveWithCost request input target tables).1.request = request.retarget input target := by
  simp only [prepareCurveWithCost, retargetDataWithCost, FieldExpr.run]
  rw [curveResultExpr_value, arrayBitsWithCost_value, tables.x7.targets.get_eq]
  rw [makeLiftsWithCost_get_fun, retargetVectorWithCost_value, vector_get_ofFn,
    tables.x7.targets.get_eq, tables.x7.quotients.get_eq]
  rfl

theorem prepareCurveWithCost_bound (request : CurveGateRequest) (input : AffineInput)
    (target : BaseField) (tables : CurveScheduleTables request) :
    (prepareCurveWithCost request input target tables).2 ≤ 12500 := by
  have bound := curveResultExpr_bound request input tables.x3.targets tables.x5.targets tables.x7.targets tables.y4.targets tables.y6.targets
  rw [FieldExpr.run_work] at bound
  simp only [prepareCurveWithCost, retargetDataWithCost_bound]
  omega

structure PreparedX where
  request : BiquadraticXRequest
  tables : XScheduleTables request

def prepareXWithCost (request : BiquadraticXRequest) (input : AffineInput)
    (target : BaseField) (tables : XScheduleTables request) : PreparedX × Nat :=
  let data := retargetDataWithCost tables.x9.targets.data tables.x9.quotients.data target
    (xResultExpr request input tables.y6.targets tables.y8.targets tables.y10.targets tables.x9.targets)
  let updated := { request with x9Targets := data.targets.get, x9Lifts := data.lifts.get }
  let views : XScheduleTables updated := {
    y6 := tables.y6
    y8 := tables.y8
    y10 := tables.y10
    x9 := {
      targets := TableView.ofVector data.targets
      quotients := tables.x9.quotients
      canonical := by
        intro index
        change (makeLiftsWithCost _ _).1.get index = _
        rw [makeLiftsWithCost_get_eq, tables.x9.quotients.get_eq] }
  }
  (⟨updated, views⟩, data.work + 128)

theorem prepareXWithCost_value (request : BiquadraticXRequest) (input : AffineInput)
    (target : BaseField) (tables : XScheduleTables request) :
    (prepareXWithCost request input target tables).1.request = request.retarget input target := by
  simp only [prepareXWithCost, retargetDataWithCost, FieldExpr.run]
  rw [xResultExpr_value, arrayBitsWithCost_value, tables.x9.targets.get_eq]
  rw [makeLiftsWithCost_get_fun, retargetVectorWithCost_value, vector_get_ofFn,
    tables.x9.targets.get_eq, tables.x9.quotients.get_eq]
  rfl

theorem prepareXWithCost_bound (request : BiquadraticXRequest) (input : AffineInput)
    (target : BaseField) (tables : XScheduleTables request) :
    (prepareXWithCost request input target tables).2 ≤ 11500 := by
  have bound := xResultExpr_bound request input tables.y6.targets tables.y8.targets tables.y10.targets tables.x9.targets
  rw [FieldExpr.run_work] at bound
  simp only [prepareXWithCost, retargetDataWithCost_bound]
  omega

structure PreparedY where
  request : BiquadraticYRequest
  tables : YScheduleTables request

def prepareYWithCost (request : BiquadraticYRequest) (input : AffineInput)
    (target : BaseField) (tables : YScheduleTables request) : PreparedY × Nat :=
  let data := retargetDataWithCost tables.x9.targets.data tables.x9.quotients.data target
    (yResultExpr request input tables.y6.targets tables.x7.targets tables.x9.targets)
  let updated := { request with x9Targets := data.targets.get, x9Lifts := data.lifts.get }
  let views : YScheduleTables updated := {
    y6 := tables.y6
    x7 := tables.x7
    x9 := {
      targets := TableView.ofVector data.targets
      quotients := tables.x9.quotients
      canonical := by
        intro index
        change (makeLiftsWithCost _ _).1.get index = _
        rw [makeLiftsWithCost_get_eq, tables.x9.quotients.get_eq] }
  }
  (⟨updated, views⟩, data.work + 128)

theorem prepareYWithCost_value (request : BiquadraticYRequest) (input : AffineInput)
    (target : BaseField) (tables : YScheduleTables request) :
    (prepareYWithCost request input target tables).1.request = request.retarget input target := by
  simp only [prepareYWithCost, retargetDataWithCost, FieldExpr.run]
  rw [yResultExpr_value, arrayBitsWithCost_value, tables.x9.targets.get_eq]
  rw [makeLiftsWithCost_get_fun, retargetVectorWithCost_value, vector_get_ofFn,
    tables.x9.targets.get_eq, tables.x9.quotients.get_eq]
  rfl

theorem prepareYWithCost_bound (request : BiquadraticYRequest) (input : AffineInput)
    (target : BaseField) (tables : YScheduleTables request) :
    (prepareYWithCost request input target tables).2 ≤ 11500 := by
  have bound := yResultExpr_bound request input tables.y6.targets tables.x7.targets tables.x9.targets
  rw [FieldExpr.run_work] at bound
  simp only [prepareYWithCost, retargetDataWithCost_bound]
  omega

structure PreparedZ where
  request : BiquadraticZRequest
  tables : ZScheduleTables request

def prepareZWithCost (request : BiquadraticZRequest) (input : AffineInput)
    (target : BaseField) (tables : ZScheduleTables request) : PreparedZ × Nat :=
  let data := retargetDataWithCost tables.x9.targets.data tables.x9.quotients.data target
    (zResultExpr request input tables.y6.targets tables.y8.targets tables.y10.targets tables.x7.targets tables.x9.targets)
  let updated := { request with x9Targets := data.targets.get, x9Lifts := data.lifts.get }
  let views : ZScheduleTables updated := {
    y6 := tables.y6
    y8 := tables.y8
    y10 := tables.y10
    x7 := tables.x7
    x9 := {
      targets := TableView.ofVector data.targets
      quotients := tables.x9.quotients
      canonical := by
        intro index
        change (makeLiftsWithCost _ _).1.get index = _
        rw [makeLiftsWithCost_get_eq, tables.x9.quotients.get_eq] }
  }
  (⟨updated, views⟩, data.work + 128)

theorem prepareZWithCost_value (request : BiquadraticZRequest) (input : AffineInput)
    (target : BaseField) (tables : ZScheduleTables request) :
    (prepareZWithCost request input target tables).1.request = request.retarget input target := by
  simp only [prepareZWithCost, retargetDataWithCost, FieldExpr.run]
  rw [zResultExpr_value, arrayBitsWithCost_value, tables.x9.targets.get_eq]
  rw [makeLiftsWithCost_get_fun, retargetVectorWithCost_value, vector_get_ofFn,
    tables.x9.targets.get_eq, tables.x9.quotients.get_eq]
  rfl

theorem prepareZWithCost_bound (request : BiquadraticZRequest) (input : AffineInput)
    (target : BaseField) (tables : ZScheduleTables request) :
    (prepareZWithCost request input target tables).2 ≤ 12500 := by
  have bound := zResultExpr_bound request input tables.y6.targets tables.y8.targets tables.y10.targets tables.x7.targets tables.x9.targets
  rw [FieldExpr.run_work] at bound
  simp only [prepareZWithCost, retargetDataWithCost_bound]
  omega


/-- This value keeps a row and the arrays that supply its schedule. -/
structure PreparedRow where
  request : BiquadraticRowRequest
  tables : RowScheduleTables request

def prepareRowWithCost (row : PreparedRow) (input : AffineInput)
    (target : FieldMacToECMac.HomogeneousValue) : PreparedRow × Nat :=
  let x := prepareXWithCost row.request.x input target.x row.tables.x
  let y := prepareYWithCost row.request.y input target.y row.tables.y
  let z := prepareZWithCost row.request.z input target.z row.tables.z
  (⟨⟨x.1.request, y.1.request, z.1.request⟩, ⟨x.1.tables, y.1.tables, z.1.tables⟩⟩,
    x.2 + y.2 + z.2 + 12)

theorem prepareRowWithCost_value (row : PreparedRow) (input : AffineInput)
    (target : FieldMacToECMac.HomogeneousValue) :
    (prepareRowWithCost row input target).1.request = row.request.retarget input target := by
  simp only [prepareRowWithCost, prepareXWithCost_value, prepareYWithCost_value,
    prepareZWithCost_value, BiquadraticRowRequest.retarget]

theorem prepareRowWithCost_bound (row : PreparedRow) (input : AffineInput)
    (target : FieldMacToECMac.HomogeneousValue) :
    (prepareRowWithCost row input target).2 ≤ 35512 := by
  have x := prepareXWithCost_bound row.request.x input target.x row.tables.x
  have y := prepareYWithCost_bound row.request.y input target.y row.tables.y
  have z := prepareZWithCost_bound row.request.z input target.z row.tables.z
  simp only [prepareRowWithCost]
  omega

/-- This traversal materializes each row once. -/
def prepareRowsWithCost {count : Nat} (rows : Vector PreparedRow count)
    (input : AffineInput) (targets : Vector FieldMacToECMac.HomogeneousValue count) :
    Vector PreparedRow count × Nat :=
  let outputs := Vector.ofFn (fun index =>
    let result := prepareRowWithCost (rows.get index) input (targets.get index)
    (result.1, result.2 + 3))
  (outputs.map Prod.fst, (outputs.toList.map Prod.snd).sum + 2 * count)

theorem prepareRowsWithCost_value {count : Nat} (rows : Vector PreparedRow count)
    (input : AffineInput) (targets : Vector FieldMacToECMac.HomogeneousValue count) :
    (prepareRowsWithCost rows input targets).1.map PreparedRow.request =
      Vector.ofFn (fun index => (rows.get index).request.retarget input (targets.get index)) := by
  apply Vector.ext
  intro index valid
  simp only [prepareRowsWithCost, Vector.getElem_map, Vector.getElem_ofFn,
    prepareRowWithCost_value]

theorem prepareRowsWithCost_bound {count : Nat} (rows : Vector PreparedRow count)
    (input : AffineInput) (targets : Vector FieldMacToECMac.HomogeneousValue count) :
    (prepareRowsWithCost rows input targets).2 ≤ 35517 * count := by
  have each : ∀ value ∈ (Vector.ofFn (fun index =>
      let result := prepareRowWithCost (rows.get index) input (targets.get index)
      (result.1, result.2 + 3))).toList.map Prod.snd, value ≤ 35515 := by
    intro value member
    simp only [Vector.toList_ofFn, List.mem_map, List.mem_ofFn] at member
    obtain ⟨pair, ⟨index, rfl⟩, rfl⟩ := member
    have bound := prepareRowWithCost_bound (rows.get index) input (targets.get index)
    omega
  have total := List.sum_le_card_nsmul _ _ each
  simp only [List.length_map, Vector.length_toList, nsmul_eq_mul, Nat.cast_id] at total
  simp only [prepareRowsWithCost]
  omega

/-- These arrays supply the original simulator requests. -/
structure SimulatorTables (state : CircuitSimulatorState) where
  curve : CurveScheduleTables state.curve
  rows : Vector PreparedRow FieldMacToECMac.outputMacCount
  requests_eq : rows.map PreparedRow.request = state.points

/-- This record caches all requests and all arrays after retargeting. -/
structure Prepared where
  curve : PreparedCurve
  points : PointGateRequests
  rows : Vector PreparedRow FieldMacToECMac.outputMacCount
  requests_eq : rows.map PreparedRow.request = points

/-- This computation materializes the curve, output targets, and point rows once. -/
def prepareWithCost [FieldCertificate] [GroupCertificate]
    (state : CircuitSimulatorState) (tables : SimulatorTables state)
    (input : AffineInput) (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) : Prepared × Nat :=
  let curve := prepareCurveWithCost state.curve input state.bridgeKey tables.curve
  let targets := outputTargetsVectorWithCost point free scales
  let rows := prepareRowsWithCost tables.rows input targets.1
  let points := rows.1.map PreparedRow.request
  (⟨curve.1, points, rows.1, rfl⟩,
    curve.2 + targets.2 + rows.2 + 2 * FieldMacToECMac.outputMacCount + 8)

theorem prepareWithCost_curve [FieldCertificate] [GroupCertificate]
    (state : CircuitSimulatorState) (tables : SimulatorTables state)
    (input : AffineInput) (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) :
    (prepareWithCost state tables input point free scales).1.curve.request =
      state.selectedCurve input :=
  prepareCurveWithCost_value state.curve input state.bridgeKey tables.curve

theorem prepareWithCost_points [FieldCertificate] [GroupCertificate]
    (state : CircuitSimulatorState) (tables : SimulatorTables state)
    (input : AffineInput) (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) :
    (prepareWithCost state tables input point free scales).1.points =
      state.selectedPoints input point free scales.get := by
  simp only [prepareWithCost, prepareRowsWithCost_value, outputTargetsVectorWithCost_value]
  unfold CircuitSimulatorState.selectedPoints retargetPointGateRequests
  congr 1
  funext index
  have same := congrArg (fun rows => rows.get index) tables.requests_eq
  simp only [Vector.get_map] at same
  rw [same]

theorem prepareWithCost_bound [FieldCertificate] [GroupCertificate]
    (state : CircuitSimulatorState) (tables : SimulatorTables state)
    (input : AffineInput) (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) :
    (prepareWithCost state tables input point free scales).2 ≤ 3421659 := by
  have curve := prepareCurveWithCost_bound state.curve input state.bridgeKey tables.curve
  have targets := outputTargetsVectorWithCost_bound point free scales
  have rows := prepareRowsWithCost_bound tables.rows input
    (outputTargetsVectorWithCost point free scales).1
  simp only [FieldMacToECMac.outputMacCount] at rows
  simp only [prepareWithCost, FieldMacToECMac.outputMacCount]
  omega


/-- This traversal materializes each row schedule and counts its vector read. -/
def Prepared.pointScheduleWithCost (prepared : Prepared)
    (input : AffineInput) (inputMac : InputMac) : List GateDirective × Nat :=
  let chunks := List.ofFn (fun index =>
    let row := prepared.rows.get index
    let result := rowScheduleWithCost row.request index input inputMac row.tables
    (result.1, result.2 + 2))
  flattenWithCost chunks

theorem Prepared.pointScheduleWithCost_value (prepared : Prepared)
    (input : AffineInput) (inputMac : InputMac) :
    (prepared.pointScheduleWithCost input inputMac).1 =
      pointGateSchedule prepared.points input inputMac := by
  simp only [Prepared.pointScheduleWithCost, flattenWithCost_value, List.map_ofFn,
    Function.comp_def, rowScheduleWithCost_value, pointGateSchedule]
  congr 2
  funext index
  have same := congrArg (fun rows => rows.get index) prepared.requests_eq
  simp only [Vector.get_map] at same
  rw [same]

theorem Prepared.pointScheduleWithCost_count (prepared : Prepared)
    (input : AffineInput) (inputMac : InputMac) :
    (prepared.pointScheduleWithCost input inputMac).2 = 7492030 := by
  simp only [Prepared.pointScheduleWithCost, flattenWithCost_count, List.map_ofFn,
    Function.comp_def, rowScheduleWithCost_count, rowScheduleWithCost_value,
    BiquadraticRowRequest.schedule_length, List.length_ofFn]
  rw [List.ofFn_const, List.ofFn_const]
  norm_num [FieldMacToECMac.outputMacCount, coordinateBitCount]

/-- This computation joins the cached curve and point schedules. -/
def Prepared.scheduleWithCost (prepared : Prepared) (input : AffineInput)
    (originalMac linkedMac : InputMac) : List GateDirective × Nat :=
  flattenWithCost [curveScheduleWithCost prepared.curve.request input originalMac
    prepared.curve.tables, prepared.pointScheduleWithCost input linkedMac]

theorem Prepared.scheduleWithCost_value (prepared : Prepared) (input : AffineInput)
    (originalMac linkedMac : InputMac) :
    (prepared.scheduleWithCost input originalMac linkedMac).1 =
      pipelineGateSchedule prepared.curve.request prepared.points input originalMac linkedMac := by
  simp only [Prepared.scheduleWithCost, flattenWithCost_value, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, curveScheduleWithCost_value,
    Prepared.pointScheduleWithCost_value, List.append_nil, pipelineGateSchedule]

theorem Prepared.scheduleWithCost_count (prepared : Prepared) (input : AffineInput)
    (originalMac linkedMac : InputMac) :
    (prepared.scheduleWithCost input originalMac linkedMac).2 = 8078530 := by
  simp only [Prepared.scheduleWithCost, flattenWithCost_count, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    curveScheduleWithCost_count, Prepared.pointScheduleWithCost_count,
    curveScheduleWithCost_value, Prepared.pointScheduleWithCost_value,
    CurveGateRequest.schedule_length, pointGateSchedule_length]
  norm_num [FieldMacToECMac.outputMacCount, coordinateBitCount]


open SimulatorSampling

/-- These views use the vectors that the gate sampler constructs. -/
def curveArrayTables (arrays : GateArrays 3 5) :
    CurveScheduleTables ((curveEquiv (gateArraysEquiv 3 5 arrays)).request) where
  x3 := {
    targets := ⟨arrays.2.2.2.get 0, rfl⟩
    quotients := ⟨arrays.2.2.1.get 0, rfl⟩
    canonical := fun _ => rfl }
  x5 := {
    targets := ⟨arrays.2.2.2.get 1, rfl⟩
    quotients := ⟨arrays.2.2.1.get 1, rfl⟩
    canonical := fun _ => rfl }
  x7 := {
    targets := ⟨arrays.2.2.2.get 2, rfl⟩
    quotients := ⟨arrays.2.2.1.get 2, rfl⟩
    canonical := fun _ => rfl }
  y4 := {
    targets := ⟨arrays.2.2.2.get 3, rfl⟩
    quotients := ⟨arrays.2.2.1.get 3, rfl⟩
    canonical := fun _ => rfl }
  y6 := {
    targets := ⟨arrays.2.2.2.get 4, rfl⟩
    quotients := ⟨arrays.2.2.1.get 4, rfl⟩
    canonical := fun _ => rfl }

/-- These views use the vectors that the gate sampler constructs. -/
def xArrayTables (arrays : GateArrays 5 4) :
    XScheduleTables ((xEquiv (gateArraysEquiv 5 4 arrays)).request) where
  y6 := {
    targets := ⟨arrays.2.2.2.get 0, rfl⟩
    quotients := ⟨arrays.2.2.1.get 0, rfl⟩
    canonical := fun _ => rfl }
  y8 := {
    targets := ⟨arrays.2.2.2.get 1, rfl⟩
    quotients := ⟨arrays.2.2.1.get 1, rfl⟩
    canonical := fun _ => rfl }
  y10 := {
    targets := ⟨arrays.2.2.2.get 2, rfl⟩
    quotients := ⟨arrays.2.2.1.get 2, rfl⟩
    canonical := fun _ => rfl }
  x9 := {
    targets := ⟨arrays.2.2.2.get 3, rfl⟩
    quotients := ⟨arrays.2.2.1.get 3, rfl⟩
    canonical := fun _ => rfl }

/-- These views use the vectors that the gate sampler constructs. -/
def yArrayTables (arrays : GateArrays 4 3) :
    YScheduleTables ((yEquiv (gateArraysEquiv 4 3 arrays)).request) where
  y6 := {
    targets := ⟨arrays.2.2.2.get 0, rfl⟩
    quotients := ⟨arrays.2.2.1.get 0, rfl⟩
    canonical := fun _ => rfl }
  x7 := {
    targets := ⟨arrays.2.2.2.get 1, rfl⟩
    quotients := ⟨arrays.2.2.1.get 1, rfl⟩
    canonical := fun _ => rfl }
  x9 := {
    targets := ⟨arrays.2.2.2.get 2, rfl⟩
    quotients := ⟨arrays.2.2.1.get 2, rfl⟩
    canonical := fun _ => rfl }

/-- These views use the vectors that the gate sampler constructs. -/
def zArrayTables (arrays : GateArrays 5 5) :
    ZScheduleTables ((zEquiv (gateArraysEquiv 5 5 arrays)).request) where
  y6 := {
    targets := ⟨arrays.2.2.2.get 0, rfl⟩
    quotients := ⟨arrays.2.2.1.get 0, rfl⟩
    canonical := fun _ => rfl }
  y8 := {
    targets := ⟨arrays.2.2.2.get 1, rfl⟩
    quotients := ⟨arrays.2.2.1.get 1, rfl⟩
    canonical := fun _ => rfl }
  y10 := {
    targets := ⟨arrays.2.2.2.get 2, rfl⟩
    quotients := ⟨arrays.2.2.1.get 2, rfl⟩
    canonical := fun _ => rfl }
  x7 := {
    targets := ⟨arrays.2.2.2.get 3, rfl⟩
    quotients := ⟨arrays.2.2.1.get 3, rfl⟩
    canonical := fun _ => rfl }
  x9 := {
    targets := ⟨arrays.2.2.2.get 4, rfl⟩
    quotients := ⟨arrays.2.2.1.get 4, rfl⟩
    canonical := fun _ => rfl }

/-- This sample retains the backing arrays for one point row. -/
abbrev RowArrays := GateArrays 5 4 × (GateArrays 4 3 × GateArrays 5 5)

def rowArraysEquiv : RowArrays ≃ RowPublicSample :=
  (Equiv.prodCongr ((gateArraysEquiv 5 4).trans xEquiv)
    (Equiv.prodCongr ((gateArraysEquiv 4 3).trans yEquiv)
      ((gateArraysEquiv 5 5).trans zEquiv))).trans rowEquiv

def RowArrays.prepared (arrays : RowArrays) : PreparedRow :=
  ⟨(rowArraysEquiv arrays).request,
    ⟨xArrayTables arrays.1, yArrayTables arrays.2.1, zArrayTables arrays.2.2⟩⟩

def arrayMapEquiv {A B : Type} (equivalence : A ≃ B) (count : Nat) :
    Vector A count ≃ Vector B count where
  toFun values := values.map equivalence
  invFun values := values.map equivalence.symm
  left_inv values := by simp
  right_inv values := by simp

/-- This sample retains all public target and quotient arrays. -/
abbrev PublicArrays := GateArrays 3 5 × Vector RowArrays FieldMacToECMac.outputMacCount

def publicArraysEquiv : PublicArrays ≃ PublicSample :=
  (Equiv.prodCongr ((gateArraysEquiv 3 5).trans curveEquiv)
    (arrayMapEquiv rowArraysEquiv FieldMacToECMac.outputMacCount)).trans publicEquiv

/-- This private coin keeps the arrays that the sampler constructs. -/
abbrev OfflineArrays := PublicArrays × (InputMacKey × BaseField)

def offlineArraysEquiv : OfflineArrays ≃ OfflineCoin :=
  Equiv.prodCongr publicArraysEquiv (Equiv.refl _)

def OfflineArrays.state (arrays : OfflineArrays) (oracle : SimulatorState) :
    CircuitSimulatorState where
  oracle := oracle
  curve := (publicArraysEquiv arrays.1).curveRequest
  points := (publicArraysEquiv arrays.1).pointRequests
  inputKey := arrays.2.1
  bridgeKey := arrays.2.2

def OfflineArrays.tables (arrays : OfflineArrays) (oracle : SimulatorState) :
    SimulatorTables (arrays.state oracle) where
  curve := curveArrayTables arrays.1.1
  rows := arrays.1.2.map RowArrays.prepared
  requests_eq := by
    simp only [Vector.map_map, OfflineArrays.state, PublicSample.pointRequests,
      publicArraysEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, publicEquiv,
      arrayMapEquiv, RowArrays.prepared, Function.comp_def]
    change _ = (arrays.1.2.map rowArraysEquiv).map RowPublicSample.request
    rw [Vector.map_map]
    rfl

def rowArrays : Code RowArrays 9158 :=
  (gateArrays 5 4).pair ((gateArrays 4 3).pair (gateArrays 5 5))

def publicArrays : Code PublicArrays 837191 :=
  (gateArrays 3 5).pair (rowArrays.vector FieldMacToECMac.outputMacCount)

def offlineArrays : Code OfflineArrays 838208 := publicArrays.pair (inputKey.pair field)

attribute [local instance] publicVectorFintype bitAdaptorTableFintype publicBitAdaptorKeyFintype
  publicInputMacKeyFintype
local instance : Nonempty BitAdaptor.Table := ⟨defaultBitAdaptorTable⟩
local instance : Nonempty PublicSample := ⟨defaultSimulatorCoin.tableSample⟩
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

theorem rowArrays_uniform : Uniform rowArrays :=
  uniform_pair (gateArrays_uniform 5 4)
    (uniform_pair (gateArrays_uniform 4 3) (gateArrays_uniform 5 5))

theorem publicArrays_uniform : Uniform publicArrays :=
  uniform_pair (gateArrays_uniform 3 5)
    (rowArrays.vector_uniform rowArrays_uniform FieldMacToECMac.outputMacCount)

theorem offlineArrays_uniform : Uniform offlineArrays :=
  uniform_pair publicArrays_uniform (uniform_pair inputKey_uniform field_uniform)

/-- The array-retaining sampler has the exact original offline coin law. -/
theorem offlineArrays_law :
    (offlineArrays.law.map offlineArraysEquiv) = offline.law := by
  have law := uniform_equiv offlineArrays_uniform offlineArraysEquiv
  unfold Uniform at law
  rw [Code.map_law] at law
  rw [law, offline_uniform]


/-- This budget counts coefficient reads and writes.
Each gate receives 16 read slots and 16 write slots for its fields, getters, and views.
The fixed allowance covers the outer records and closure captures. -/
def gateArrayViewWork (coefficients gates : Nat) : Nat :=
  2 * coefficients + 32 * gates + 64

/-- This computation constructs the curve request and its direct array views. -/
def curveArrayPreparedWithCost (arrays : GateArrays 3 5) : PreparedCurve × Nat :=
  (⟨(curveEquiv (gateArraysEquiv 3 5 arrays)).request, curveArrayTables arrays⟩,
    gateArrayViewWork 3 5)

/-- This computation constructs three request records and their direct array views. -/
def rowArrayPreparedWithCost (arrays : RowArrays) : PreparedRow × Nat :=
  (arrays.prepared, gateArrayViewWork 5 4 + gateArrayViewWork 4 3 + gateArrayViewWork 5 5 + 12)

/-- This record stores the original state and its materialized request views. -/
structure OfflinePrepared where
  state : CircuitSimulatorState
  tables : SimulatorTables state

/-- This traversal constructs every request once and caches the request vector. -/
def prepareOfflineWithCost (arrays : OfflineArrays) (oracle : SimulatorState) :
    OfflinePrepared × Nat :=
  let curve := curveArrayPreparedWithCost arrays.1.1
  let chunks := arrays.1.2.map (fun row =>
    let result := rowArrayPreparedWithCost row
    (result.1, result.2 + 2))
  let rows := chunks.map Prod.fst
  let points := rows.map PreparedRow.request
  let state : CircuitSimulatorState :=
    ⟨oracle, curve.1.request, points, arrays.2.1, arrays.2.2⟩
  let tables : SimulatorTables state := ⟨curve.1.tables, rows, rfl⟩
  (⟨state, tables⟩,
    curve.2 + (chunks.toList.map Prod.snd).sum + 4 * FieldMacToECMac.outputMacCount + 16)

theorem prepareOfflineWithCost_value (arrays : OfflineArrays) (oracle : SimulatorState) :
    (prepareOfflineWithCost arrays oracle).1.state = arrays.state oracle := by
  simp only [prepareOfflineWithCost, curveArrayPreparedWithCost, rowArrayPreparedWithCost,
    OfflineArrays.state, publicArraysEquiv, PublicSample.curveRequest,
    PublicSample.pointRequests, Equiv.trans_apply, Equiv.prodCongr_apply,
    publicEquiv, arrayMapEquiv, Vector.map_map, RowArrays.prepared, Function.comp_def]
  dsimp
  rw [Vector.map_map]
  rfl

theorem prepareOfflineWithCost_count (arrays : OfflineArrays) (oracle : SimulatorState) :
    (prepareOfflineWithCost arrays oracle).2 = 56848 := by
  simp only [prepareOfflineWithCost, curveArrayPreparedWithCost, rowArrayPreparedWithCost,
    gateArrayViewWork, Vector.toList_map, List.map_map, Function.comp_def]
  rw [List.map_const', List.sum_replicate_nat]
  norm_num [Vector.length_toList, FieldMacToECMac.outputMacCount]

end Kriterion.ArgoMAC.Security.SimulatorScheduleCost
