import Proof.Privacy.Simulator.Arithmetic.EncLinkSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SimulatorMachine
noncomputable section

/-- The typed observer reads the two 254-label coordinates from private RAM. -/
def encLinkOutputMac (memory : Memory) (output : Nat) : InputMac :=
  ⟨Vector.ofFn (fun index => (memory.ram (BitVec.ofNat 256 (output + index.val))).setWidth 128),
    Vector.ofFn (fun index => (memory.ram (BitVec.ofNat 256 (output + 254 + index.val))).setWidth 128)⟩

/-- The typed observer retains cutoff failure and the complete finite family. -/
def encLinkTypedValue (output : Nat) (result : EncLinkResult) : Option (InputMac × SparseOracleFamily) :=
  if result.1.2.2 = 7467 then none else some (encLinkOutputMac result.1.1 output, result.2)

/-- The recursive output list has the same consecutive word indices as the vector observer. -/
theorem encLinkOutput_ofFn (memory : Memory) (output count : Nat) :
    encLinkOutput memory output count = List.ofFn (fun index : Fin count =>
      (memory.ram (BitVec.ofNat 256 (output + index.val))).setWidth 128) := by
  induction count generalizing output with
  | zero => simp only [encLinkOutput, List.ofFn_zero]
  | succ count ih =>
      rw [encLinkOutput, List.ofFn_succ, ih]
      simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]

/-- Adjacent output arrays combine into their complete consecutive array. -/
theorem encLinkOutput_append (memory : Memory) (output first second : Nat) :
    encLinkOutput memory output (first + second) =
      encLinkOutput memory output first ++ encLinkOutput memory (output + first) second := by
  induction first generalizing output with
  | zero => simp only [Nat.zero_add, encLinkOutput, List.nil_append, Nat.add_zero]
  | succ first ih =>
      rw [Nat.succ_add, encLinkOutput, encLinkOutput, List.cons_append, ih]
      simp only [Nat.add_assoc, Nat.add_comm 1]

/-- The typed output serializes to exactly the complete stored array. -/
theorem encLinkOutputMac_words (memory : Memory) (output : Nat) :
    encLinkMacWords (encLinkOutputMac memory output) = encLinkOutput memory output 508 := by
  unfold encLinkMacWords encLinkOutputMac
  rw [Vector.toList_ofFn, Vector.toList_ofFn]
  change _ = encLinkOutput memory output (254 + 254)
  rw [encLinkOutput_append, encLinkOutput_ofFn, encLinkOutput_ofFn]

/-- The serialized input MAC determines both typed coordinates. -/
theorem encLinkMacWords_injective : Function.Injective encLinkMacWords := by
  intro first second same
  have parts := List.append_inj same (by simp)
  have x := Vector.toList_inj.mp parts.1
  have y := Vector.toList_inj.mp parts.2
  cases first
  cases second
  cases x
  cases y
  rfl

/-- The typed observer has exactly the existing array observation. -/
theorem encLinkTypedValue_words (output : Nat) (result : EncLinkResult) :
    (encLinkTypedValue output result).map (fun value => (encLinkMacWords value.1, value.2)) =
      encLinkLoopValue output 508 result := by
  unfold encLinkTypedValue encLinkLoopValue
  split
  · rfl
  · simp only [Option.map_some, encLinkOutputMac_words]

/-- An injective observation preserves equality of discrete source distributions. -/
theorem pmfMap_injective {A B : Type} [Nonempty A] (convert : A → B) (injective : Function.Injective convert) :
    Function.Injective (PMF.map convert) := by
  intro first second same
  have law := congrArg (PMF.map (Function.invFun convert)) same
  have inverse : Function.invFun convert ∘ convert = id := funext (Function.leftInverse_invFun injective)
  simpa only [PMF.map_comp, inverse, PMF.map_id] using law

/-- Equality of the array laws gives equality of the complete typed output laws. -/
theorem encLinkTypedValue_source (output : Nat) (source : PMF EncLinkResult)
    (target : PMF (Option (InputMac × SparseOracleFamily)))
    (same : source.map (encLinkLoopValue output 508) =
      target.map (Option.map fun result => (encLinkMacWords result.1, result.2))) :
    source.map (encLinkTypedValue output) = target := by
  apply pmfMap_injective (Option.map fun result : InputMac × SparseOracleFamily => (encLinkMacWords result.1, result.2))
    (Option.map_injective (by
      intro first second equal
      have parts := Prod.mk.inj equal
      exact Prod.ext (encLinkMacWords_injective parts.1) parts.2))
  rw [PMF.map_comp]
  have observe : (Option.map fun result : InputMac × SparseOracleFamily => (encLinkMacWords result.1, result.2)) ∘
      encLinkTypedValue output = encLinkLoopValue output 508 := funext (encLinkTypedValue_words output)
  rw [observe, same]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
