import Proof.Privacy.Simulator.SimulatorScheduleCost
import Proof.Privacy.Simulator.SimulatorProtocol

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography SimulatorSampling SimulatorScheduleCost
namespace SimulatorMachine
namespace Implementation

/-- This cache retains the sampled arrays behind the semantic private coin. -/
structure PrivateCache where
  coin : OfflineCoin
  tables : SimulatorTables (privateView coin)

private theorem cache_state (arrays : OfflineArrays) :
    (prepareOfflineWithCost arrays (privateView (offlineArraysEquiv arrays)).oracle).1.state =
      privateView (offlineArraysEquiv arrays) := by
  rw [prepareOfflineWithCost_value]
  rfl

/-- This transport changes only the proof that identifies the cached state. -/
def cacheWithCost (arrays : OfflineArrays) : PrivateCache × Nat :=
  let prepared := prepareOfflineWithCost arrays (privateView (offlineArraysEquiv arrays)).oracle
  (⟨offlineArraysEquiv arrays, cache_state arrays ▸ prepared.1.tables⟩, prepared.2)

theorem cacheWithCost_coin (arrays : OfflineArrays) :
    (cacheWithCost arrays).1.coin = offlineArraysEquiv arrays := rfl

theorem cacheWithCost_count (arrays : OfflineArrays) :
    (cacheWithCost arrays).2 = 56848 :=
  prepareOfflineWithCost_count arrays (privateView (offlineArraysEquiv arrays)).oracle

theorem rowArrays_drawSizeLe : rowArrays.DrawSizeLe (2 ^ 256) :=
  Code.pair_drawSizeLe _ _ (gateArrays_drawSizeLe 5 4)
    (Code.pair_drawSizeLe _ _ (gateArrays_drawSizeLe 4 3) (gateArrays_drawSizeLe 5 5))

theorem publicArrays_drawSizeLe : publicArrays.DrawSizeLe (2 ^ 256) :=
  Code.pair_drawSizeLe _ _ (gateArrays_drawSizeLe 3 5)
    (Code.vector_drawSizeLe _ rowArrays_drawSizeLe _)

/-- Every draw in the retained-array sampler has at most 256 range bits. -/
theorem offlineArrays_drawSizeLe : offlineArrays.DrawSizeLe (2 ^ 256) := by
  have keyBound : key.DrawSizeLe (2 ^ 256) := Code.map_drawSizeLe _ _
    (Code.pair_drawSizeLe _ _ (bits_drawSizeLe (by decide)) (bits_drawSizeLe (by decide)))
  apply Code.pair_drawSizeLe
  · exact publicArrays_drawSizeLe
  · apply Code.pair_drawSizeLe
    · exact Code.map_drawSizeLe _ _ (Code.pair_drawSizeLe _ _
        (key.vector_drawSizeLe keyBound _) (key.vector_drawSizeLe keyBound _))
    · exact field_drawSizeLe

end Implementation
end SimulatorMachine
end Kriterion.ArgoMAC.Security
