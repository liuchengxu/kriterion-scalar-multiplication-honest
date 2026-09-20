import Proof.Privacy.Simulator.SimulatorSamplingCost
import Proof.Privacy.Simulator.SimulatorPublicCost

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography SimulatorSampling SimulatorScheduleCost
namespace SimulatorMachine.Implementation

/-- This value pairs the cached private state with the public table. -/
def ready (arrays : OfflineArrays) : PrivateCache × Pipeline.Table :=
  ((cacheWithCost arrays).1, (tableWithCost arrays).1)

/-- This sampler retains the original private sample distribution. -/
def offlineReady : Code (PrivateCache × Pipeline.Table) 838208 := offlineArrays.map ready

/-- Each gate record has four array getter fields. The charge covers their reads,
getter closures, product temporaries, and output record writes. -/
def curveCoinWithCost (arrays : GateArrays 3 5) : CurvePublicSample × Nat :=
  (curveEquiv (gateArraysEquiv 3 5 arrays), 32)

/-- The row conversion builds three gate records and one row record. -/
def rowCoinWithCost (arrays : RowArrays) : RowPublicSample × Nat :=
  let x := (xEquiv (gateArraysEquiv 5 4 arrays.1), 32)
  let y := (yEquiv (gateArraysEquiv 4 3 arrays.2.1), 32)
  let z := (zEquiv (gateArraysEquiv 5 5 arrays.2.2), 32)
  (rowEquiv (x.1, y.1, z.1), x.2 + y.2 + z.2 + 4)

/-- This traversal materializes the public coin once. It charges both array maps. -/
def coinWithCost (arrays : OfflineArrays) : OfflineCoin × Nat :=
  let curve := curveCoinWithCost arrays.1.1
  let chunks := arrays.1.2.map fun row =>
    let result := rowCoinWithCost row
    (result.1, result.2 + 2)
  let rows := chunks.map Prod.fst
  ((publicEquiv (curve.1, rows), arrays.2),
    curve.2 + (chunks.toList.map Prod.snd).sum + 2 * FieldMacToECMac.outputMacCount + 12)

theorem coinWithCost_value (arrays : OfflineArrays) :
    (coinWithCost arrays).1 = offlineArraysEquiv arrays := by
  simp only [coinWithCost, curveCoinWithCost, rowCoinWithCost, Vector.map_map,
    offlineArraysEquiv, publicArraysEquiv, Equiv.prodCongr_apply,
    arrayMapEquiv, rowArraysEquiv, Function.comp_def]
  rfl

theorem coinWithCost_count (arrays : OfflineArrays) : (coinWithCost arrays).2 = 9508 := by
  simp only [coinWithCost, curveCoinWithCost, rowCoinWithCost, Vector.toList_map,
    List.map_map, Function.comp_def]
  rw [List.map_const', List.sum_replicate_nat]
  norm_num [Vector.length_toList, FieldMacToECMac.outputMacCount]

/-- This cache constructor uses the public coin that the caller already built. -/
def cacheFromCoinWithCost (arrays : OfflineArrays) (coin : OfflineCoin)
    (same : coin = offlineArraysEquiv arrays) : PrivateCache × Nat :=
  let oracle : SimulatorState := {
    fixedOracle := ⟨fun _ => Equiv.refl _⟩
    encOracle := ⟨fun _ => Equiv.refl _⟩
    hashOracle := fun _ => (0, 0)
    fixedTranscript := [], encTranscript := [], hashTranscript := []
    commitments := [], linking := none, bad := false }
  let prepared := prepareOfflineWithCost arrays oracle
  let stateSame : prepared.1.state = privateView coin := by
    rw [prepareOfflineWithCost_value, same]
    rfl
  (⟨coin, stateSame ▸ prepared.1.tables⟩, prepared.2)

theorem cacheFromCoinWithCost_value (arrays : OfflineArrays) (coin : OfflineCoin)
    (same : coin = offlineArraysEquiv arrays) :
    cacheFromCoinWithCost arrays coin same = cacheWithCost arrays := by
  subst coin
  rfl

/-- This callback constructs each coin, cache, and public table once. -/
def readyWithCost (arrays : OfflineArrays) : (PrivateCache × Pipeline.Table) × Nat :=
  let coin := coinWithCost arrays
  let cache := cacheFromCoinWithCost arrays coin.1 (coinWithCost_value arrays)
  let table := tableWithCost arrays
  ((cache.1, table.1), coin.2 + cache.2 + table.2)

theorem readyWithCost_value (arrays : OfflineArrays) : (readyWithCost arrays).1 = ready arrays := by
  simp only [readyWithCost, cacheFromCoinWithCost_value, ready]

theorem readyWithCost_count (arrays : OfflineArrays) : (readyWithCost arrays).2 = 81055 := by
  simp only [readyWithCost, cacheFromCoinWithCost_value, coinWithCost_count,
    cacheWithCost_count, tableWithCost_count]

end SimulatorMachine.Implementation
end Kriterion.ArgoMAC.Security
