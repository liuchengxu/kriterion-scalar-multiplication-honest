import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingWitness
import Proof.Privacy.Simulator.Arithmetic.OutputTargetsSource
import Proof.Privacy.Simulator.Arithmetic.PrivateScheduleInjective

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.SimulatorSampling
noncomputable section
attribute [local irreducible] onlineWords onlineSamplingMemory storeDrawWords online

/-- The canonical word identifies one nonzero field value. -/
theorem nonZeroBase_word_injective :
    Function.Injective (fun scale : BN254.NonZeroBase => BitVec.ofNat 256 scale.value.val) := by
  intro a b same
  have values : a.value = b.value := fieldSchedule_injective (congrArg (fun word : Word => [word]) same)
  cases a
  cases b
  cases values
  rfl

/-- The complete online word sequence identifies every point and scale. -/
theorem onlineWords_injective [BN254.FieldCertificate] : Function.Injective onlineWords := by
  intro a b same
  let ram := storeDrawWords 0 0 (fun _ => 0) (onlineWords a)
  have storedA : WordsAt ram 0 0 (onlineWords a) := wordsAt_store _ _ _ _ (by rw [onlineWords_length]; decide)
  have storedB : WordsAt ram 0 0 (onlineWords b) := by rw [← same]; exact storedA
  apply Prod.ext
  · funext index
    have first := onlineWords_point 0 (fun _ => 0) a index
    have second := onlineWords_point 0 (fun _ => 0) b index
    rw [← same] at second
    exact Option.some.inj (first.symm.trans second)
  · funext index
    exact nonZeroBase_word_injective
      ((onlineWords_scale ram 0 a storedA index).symm.trans (onlineWords_scale ram 0 b storedB index))

/-- The stored online RAM identifies one typed source coin. -/
theorem onlineStored_injective [BN254.FieldCertificate] (base : Memory) :
    Function.Injective (fun coin => storeDrawWords (base.registers 10) 0 base.ram (onlineWords coin)) := by
  intro a b same
  change storeDrawWords (base.registers 10) 0 base.ram (onlineWords a) =
    storeDrawWords (base.registers 10) 0 base.ram (onlineWords b) at same
  apply onlineWords_injective
  apply List.ext_getElem ((onlineWords_length a).trans (onlineWords_length b).symm)
  intro index aInside bInside
  have aFits : 0 + (onlineWords a).length ≤ 2 ^ 256 := by rw [onlineWords_length]; decide
  have bFits : 0 + (onlineWords b).length ≤ 2 ^ 256 := by rw [onlineWords_length]; decide
  rw [← storeDrawWords_get (base.registers 10) 0 base.ram (onlineWords a) index aInside aFits,
    same, storeDrawWords_get (base.registers 10) 0 base.ram (onlineWords b) index bInside bFits]

/-- This proof decoder reads the unique typed coin from a stored RAM image. -/
def onlineMemoryCoin [BN254.FieldCertificate] (base : Memory) (ram : Word → Word) :
    (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase) :=
  Function.invFun (fun coin => storeDrawWords (base.registers 10) 0 base.ram (onlineWords coin)) ram

/-- The proof decoder returns the exact stored online coin. -/
theorem onlineMemoryCoin_stored [BN254.FieldCertificate] (base : Memory)
    (coin : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase)) :
    onlineMemoryCoin base (storeDrawWords (base.registers 10) 0 base.ram (onlineWords coin)) = coin :=
  Function.leftInverse_invFun (onlineStored_injective base) coin

/-- The supported witness and the RAM decoder select the same typed online coin. -/
theorem onlineSamplingCoin_decode [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (base : Memory) (result : Memory × Nat)
    (supported : result ∈ (onlineSamplingMemory attempts base).support) :
    onlineSamplingCoin attempts base result = onlineMemoryCoin base result.1.ram := by
  obtain ⟨coin, _, memory⟩ := onlineSamplingMemory_witness attempts base result.1 result.2 supported
  have witness := onlineSamplingCoin_words attempts base result supported
  rw [memory, onlineMemoryCoin_stored]
  apply onlineWords_injective
  apply List.ext_getElem ((onlineWords_length _).trans (onlineWords_length coin).symm)
  intro index selectedInside coinInside
  have word := witness index selectedInside
  rw [memory, storeDrawWords_get (base.registers 10) 0 base.ram (onlineWords coin) index coinInside
    (by rw [onlineWords_length]; decide)] at word
  exact word.symm

/-- The selected witness has the exact online total-sampling marginal. -/
theorem onlineSamplingCoin_source [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (base : Memory) :
    (onlineSamplingMemory attempts base).map (onlineSamplingCoin attempts base) = (online.total attempts).law := by
  calc
    _ = (onlineSamplingMemory attempts base).map (fun result => onlineMemoryCoin base result.1.ram) := by
      change (onlineSamplingMemory attempts base).bind _ = (onlineSamplingMemory attempts base).bind _
      apply Security.ThreePhase.bind_eq_on_support
      intro result supported
      exact congrArg PMF.pure (onlineSamplingCoin_decode attempts base result supported)
    _ = _ := by
      have law := congrArg (PMF.map (onlineMemoryCoin base)) (onlineSamplingMemory_source attempts base)
      simp only [PMF.map_comp, Function.comp_def, onlineMemoryCoin_stored] at law
      exact law.trans (PMF.map_id _)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
