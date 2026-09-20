import Proof.Privacy.Simulator.Arithmetic.HashHandler
import Proof.Privacy.Simulator.Arithmetic.InstallFreshState

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The first-match RAM search agrees with the represented pair list. -/
theorem findTable_represents (ram : Word → Word) (address key : Word) (pairs : List (Word × Word))
    (represented : RepresentsPairs ram address pairs) :
    findTable pairs.length ram address key = pairs.lookup key := by
  induction pairs generalizing address with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨left, right⟩
      rcases represented with ⟨storedLeft, storedRight, storedRest⟩
      by_cases equal : left = key
      · subst key
        simp [findTable, storedLeft, storedRight, List.lookup]
      · have different : key ≠ left := Ne.symm equal
        have compared : (key == left) = false := beq_eq_false_iff_ne.mpr different
        simpa [findTable, storedLeft, equal, different, compared, List.lookup] using ih (address + 2#256) storedRest

/-- The hash insertion preserves the old table and prepends the sampled key-value pair. -/
theorem hashInstalled_represents (memory : Memory) (pairs : List (Word × Word))
    (represented : RepresentsPairs memory.ram (memory.registers 5) pairs)
    (fits : 2 * pairs.length + 2 ≤ 2 ^ 256) :
    RepresentsPairs (hashInstalled memory).ram ((hashInstalled memory).registers 1)
      ((memory.registers 8, memory.registers 0) :: pairs) := by
  exact RepresentsPairs.prepend memory.ram (memory.registers 5 - 2#256)
    (memory.registers 8) (memory.registers 0) pairs (by simpa using represented) fits

/-- The committed hash answer uses the stored value or one exact uniform machine word. -/
theorem hashTailSamples_reply (memory : Memory) :
    (hashTailSamples memory).map (fun result => result.1.registers 8) =
      match tableResult memory with
      | some value => PMF.pure value
      | none => PMF.uniformOfFintype Word := by
  by_cases fresh : memory.registers 12 = 0#256
  · simp [hashTailSamples, tableResult, fresh, PMF.map_comp, Function.comp_def,
      oracleCommitted, hashInstalled, frame]
    change (coinFold 256 0).map id = _
    rw [PMF.map_id, coinFold_word_uniform]
  · simp [hashTailSamples, tableResult, fresh, PMF.pure_map, oracleCommitted, hashFound]

/-- The hash handler always returns a success flag because it needs no rejection sampler. -/
theorem hashTailSamples_success (memory : Memory) :
    (hashTailSamples memory).map (fun result => result.1.registers 7) = PMF.pure (1#256 : Word) := by
  by_cases fresh : memory.registers 12 = 0#256
  · simp [hashTailSamples, fresh, PMF.map_comp, Function.comp_def, oracleCommitted, hashInstalled]
    exact PMF.map_const _ _
  · simp [hashTailSamples, fresh, PMF.pure_map, oracleCommitted, hashFound]

/-- The complete hash source preserves the first-match reply law. -/
theorem hashHandlerSamples_reply (count : Nat) (memory : Memory) :
    (hashHandlerSamples count memory).map (fun result => result.1.registers 8) =
      match findTable count (oracleLoaded memory).ram ((oracleLoaded memory).registers 1)
          ((oracleLoaded memory).registers 8) with
      | some value => PMF.pure value
      | none => PMF.uniformOfFintype Word := by
  unfold hashHandlerSamples
  rw [PMF.map_comp]
  change (hashTailSamples (hashScan count memory).1).map (fun result => result.1.registers 8) = _
  rw [hashTailSamples_reply]
  change (match tableResult (tableScan count (tableInitial (hashReady (oracleLoaded memory)))).1 with
    | some value => PMF.pure value
    | none => PMF.uniformOfFintype Word) = _
  rw [tableScan_source]
  simp [tableInitial, hashReady]

/-- The actual machine returns the represented hash value or one exact uniform fresh value. -/
theorem hashHandler_source [BN254.FieldCertificate] (pairs : List (Word × Word)) (memory : Memory)
    (fits : pairs.length < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 pairs.length)
    (represented : RepresentsPairs (oracleLoaded memory).ram ((oracleLoaded memory).registers 1) pairs) :
    (run hashHandler ((hashScan pairs.length memory).2 + 1845) ⟨0, memory⟩).map
      (Option.map fun result => result.1.memory.registers 8) =
      (match pairs.lookup ((oracleLoaded memory).registers 8) with
        | some value => PMF.pure value
        | none => PMF.uniformOfFintype Word).map some := by
  rw [hashHandler_run pairs.length memory fits counter, PMF.map_comp]
  have replies := hashHandlerSamples_reply pairs.length memory
  rw [findTable_represents _ _ _ pairs represented] at replies
  have projected := congrArg (PMF.map some) replies
  simpa only [PMF.map_comp, Function.comp_def, Option.map_some] using projected

end Kriterion.ArgoMAC.ArithmeticSimulator
