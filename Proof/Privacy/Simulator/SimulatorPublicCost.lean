import Proof.Privacy.Simulator.SimulatorPrivateCache

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography SimulatorScheduleCost SimulatorSampling
namespace SimulatorMachine
namespace Implementation

/-- This instruction allows three array or record reads, one option constructor,
and one table-field write. -/
def someFieldWithCost {A : Type} (value : A) : Option A × Nat := (some value, 5)

/-- This instruction writes one absent table field. -/
def noneFieldWithCost (A : Type) : Option A × Nat := (none, 1)

/-- This computation reads the sampled arrays and writes all eleven public fields. -/
def xTableWithCost (arrays : GateArrays 5 4) : Biquadratic.Table × Nat :=
  let c0 := someFieldWithCost (arrays.1.get 0)
  let c1 := someFieldWithCost (arrays.1.get 1)
  let c2 := someFieldWithCost (arrays.1.get 2)
  let c3 := someFieldWithCost (arrays.1.get 3)
  let c4 := noneFieldWithCost _
  let c5 := someFieldWithCost (arrays.1.get 4)
  let x7 := noneFieldWithCost _
  let x9 := someFieldWithCost (arrays.2.1.get 3)
  let y6 := someFieldWithCost (arrays.2.1.get 0)
  let y8 := someFieldWithCost (arrays.2.1.get 1)
  let y10 := someFieldWithCost (arrays.2.1.get 2)
  (⟨c0.1, c1.1, c2.1, c3.1, c4.1, c5.1, x7.1, x9.1, y6.1, y8.1, y10.1⟩,
    c0.2 + c1.2 + c2.2 + c3.2 + c4.2 + c5.2 + x7.2 + x9.2 + y6.2 + y8.2 + y10.2)

theorem xTableWithCost_value (arrays : GateArrays 5 4) :
    (xTableWithCost arrays).1 = (xEquiv (gateArraysEquiv 5 4 arrays)).request.table := rfl

theorem xTableWithCost_count (arrays : GateArrays 5 4) :
    (xTableWithCost arrays).2 = 47 := rfl

/-- This computation reads the sampled arrays and writes all eleven public fields. -/
def yTableWithCost (arrays : GateArrays 4 3) : Biquadratic.Table × Nat :=
  let c0 := someFieldWithCost (arrays.1.get 0)
  let c1 := someFieldWithCost (arrays.1.get 1)
  let c2 := noneFieldWithCost _
  let c3 := noneFieldWithCost _
  let c4 := someFieldWithCost (arrays.1.get 2)
  let c5 := someFieldWithCost (arrays.1.get 3)
  let x7 := someFieldWithCost (arrays.2.1.get 1)
  let x9 := someFieldWithCost (arrays.2.1.get 2)
  let y6 := someFieldWithCost (arrays.2.1.get 0)
  let y8 := noneFieldWithCost _
  let y10 := noneFieldWithCost _
  (⟨c0.1, c1.1, c2.1, c3.1, c4.1, c5.1, x7.1, x9.1, y6.1, y8.1, y10.1⟩,
    c0.2 + c1.2 + c2.2 + c3.2 + c4.2 + c5.2 + x7.2 + x9.2 + y6.2 + y8.2 + y10.2)

theorem yTableWithCost_value (arrays : GateArrays 4 3) :
    (yTableWithCost arrays).1 = (yEquiv (gateArraysEquiv 4 3 arrays)).request.table := rfl

theorem yTableWithCost_count (arrays : GateArrays 4 3) :
    (yTableWithCost arrays).2 = 39 := rfl

/-- This computation reads the sampled arrays and writes all eleven public fields. -/
def zTableWithCost (arrays : GateArrays 5 5) : Biquadratic.Table × Nat :=
  let c0 := someFieldWithCost (arrays.1.get 0)
  let c1 := noneFieldWithCost _
  let c2 := someFieldWithCost (arrays.1.get 1)
  let c3 := someFieldWithCost (arrays.1.get 2)
  let c4 := someFieldWithCost (arrays.1.get 3)
  let c5 := someFieldWithCost (arrays.1.get 4)
  let x7 := someFieldWithCost (arrays.2.1.get 3)
  let x9 := someFieldWithCost (arrays.2.1.get 4)
  let y6 := someFieldWithCost (arrays.2.1.get 0)
  let y8 := someFieldWithCost (arrays.2.1.get 1)
  let y10 := someFieldWithCost (arrays.2.1.get 2)
  (⟨c0.1, c1.1, c2.1, c3.1, c4.1, c5.1, x7.1, x9.1, y6.1, y8.1, y10.1⟩,
    c0.2 + c1.2 + c2.2 + c3.2 + c4.2 + c5.2 + x7.2 + x9.2 + y6.2 + y8.2 + y10.2)

theorem zTableWithCost_value (arrays : GateArrays 5 5) :
    (zTableWithCost arrays).1 = (zEquiv (gateArraysEquiv 5 5 arrays)).request.table := rfl

theorem zTableWithCost_count (arrays : GateArrays 5 5) :
    (zTableWithCost arrays).2 = 51 := rfl

/-- This computation allows nine record reads and three row-field writes. -/
def rowTableWithCost (arrays : RowArrays) : FieldMacToECMac.RowTable × Nat :=
  let x := xTableWithCost arrays.1
  let y := yTableWithCost arrays.2.1
  let z := zTableWithCost arrays.2.2
  (⟨x.1, y.1, z.1⟩, x.2 + y.2 + z.2 + 12)

theorem rowTableWithCost_value (arrays : RowArrays) :
    (rowTableWithCost arrays).1 = (rowArraysEquiv arrays).request.table := rfl

theorem rowTableWithCost_count (arrays : RowArrays) :
    (rowTableWithCost arrays).2 = 149 := by simp only [rowTableWithCost, xTableWithCost_count, yTableWithCost_count, zTableWithCost_count]

/-- Each curve field allows three array or record reads and one field write. -/
def curveTableWithCost (arrays : GateArrays 3 5) : CurveMembership.Table × Nat :=
  (⟨arrays.1.get 0, arrays.1.get 1, arrays.1.get 2, arrays.2.1.get 0,
    arrays.2.1.get 1, arrays.2.1.get 2, arrays.2.1.get 3, arrays.2.1.get 4⟩, 32)

theorem curveTableWithCost_value (arrays : GateArrays 3 5) :
    (curveTableWithCost arrays).1 = (curveEquiv (gateArraysEquiv 3 5 arrays)).request.table := rfl

theorem curveTableWithCost_count (arrays : GateArrays 3 5) :
    (curveTableWithCost arrays).2 = 32 := rfl

/-- This computation materializes every row and the three public coordinate vectors.
The table shares the sampled inner vectors. The counter excludes serialization. -/
def tableWithCost (arrays : OfflineArrays) : Pipeline.Table × Nat :=
  let curve := curveTableWithCost arrays.1.1
  let rows := arrays.1.2.map (fun row =>
    let result := rowTableWithCost row
    (result.1, result.2 + 3))
  let x := rows.map (fun row => row.1.x)
  let y := rows.map (fun row => row.1.y)
  let z := rows.map (fun row => row.1.z)
  (⟨curve.1, ⟨x, y, z⟩⟩,
    curve.2 + (rows.toList.map Prod.snd).sum + 9 * FieldMacToECMac.outputMacCount + 16)

theorem tableWithCost_value (arrays : OfflineArrays) :
    (tableWithCost arrays).1 = (privateView (offlineArraysEquiv arrays)).table := by
  have rows (projection : FieldMacToECMac.RowTable → Biquadratic.Table) :
      arrays.1.2.map (fun row => projection (rowTableWithCost row).1) =
        Vector.ofFn (fun index => projection
          ((privateView (offlineArraysEquiv arrays)).points.get index).table) := by
    apply Vector.ext
    intro index valid
    simp only [Vector.getElem_map, Vector.getElem_ofFn, rowTableWithCost_value]
    change _ = projection (((arrays.1.2.map rowArraysEquiv).map RowPublicSample.request).get
      ⟨index, valid⟩).table
    simp only [Vector.get_map]
    rfl
  simp only [tableWithCost, curveTableWithCost_value, CircuitSimulatorState.table,
    pointGateTable, Vector.map_map, Function.comp_def]
  rw [rows, rows, rows]
  rfl

theorem tableWithCost_count (arrays : OfflineArrays) :
    (tableWithCost arrays).2 = 14699 := by
  simp only [tableWithCost, curveTableWithCost_count, rowTableWithCost_count,
    Vector.toList_map, List.map_map, Function.comp_def]
  rw [List.map_const', List.sum_replicate_nat]
  norm_num [Vector.length_toList, FieldMacToECMac.outputMacCount]

end Implementation
end SimulatorMachine
end Kriterion.ArgoMAC.Security
