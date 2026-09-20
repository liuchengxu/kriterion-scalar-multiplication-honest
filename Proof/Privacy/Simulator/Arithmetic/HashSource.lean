import Proof.Privacy.Simulator.Arithmetic.HashEncoding

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The scan setup retains the table address and the query operand. -/
theorem hashReady_result (count : Nat) (memory : Memory) :
    tableResult (tableScan count (tableInitial (hashReady memory))).1 =
      findTable count memory.ram (memory.registers 1) (memory.registers 8) := by
  rw [tableScan_source]
  simp [tableInitial, hashReady]

/-- The hash scan uses the loaded input table and the saved operand. -/
theorem hashScan_result (count : Nat) (memory : Memory) :
    tableResult (hashScan count memory).1 =
      findTable count (oracleLoaded memory).ram ((oracleLoaded memory).registers 1)
        ((oracleLoaded memory).registers 8) := by
  exact hashReady_result count (oracleLoaded memory)

/-- The encoded hash scan returns the same optional answer as the finite source table. -/
theorem hashScan_lookup {Key : Type} [DecidableEq Key] (encode : Key → Word)
    (injective : Function.Injective encode) (pairs : HashTable Key (2 ^ 256)) (key : Key)
    (memory : Memory) (oracle : Fin 15749)
    (represented : HashMemory memory.ram oracle (hashWordPairs encode pairs))
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = encode key) (fits : 2 * pairs.length ≤ 2 ^ 110) :
    tableResult (hashScan pairs.length memory).1 =
      (pairs.lookup key).map (fun value => BitVec.ofNat 256 value.val) := by
  have length : (hashWordPairs encode pairs).length = pairs.length := by simp [hashWordPairs]
  have loaded := represented.loaded memory oracle (hashWordPairs encode pairs) (by simpa only [length] using fits)
  have base := oracleLoaded_inputBase memory oracle pairs.length index (by simpa only [length] using represented.count) fits
  rw [hashScan_result]
  rw [base, (oracleLoaded_query memory).1, operand]
  rw [← length, findTable_represents _ _ _ _ loaded.stored, hashWordPairs_lookup encode injective]

/-- The compiled hash reply has the exact finite source distribution. -/
theorem hashHandlerSamples_finite {Key : Type} [DecidableEq Key] (encode : Key → Word)
    (injective : Function.Injective encode) (pairs : HashTable Key (2 ^ 256)) (key : Key)
    (memory : Memory) (oracle : Fin 15749)
    (represented : HashMemory memory.ram oracle (hashWordPairs encode pairs))
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = encode key) (fits : 2 * pairs.length ≤ 2 ^ 110) :
    (hashHandlerSamples pairs.length memory).map (fun result => (result.1.registers 8).toFin) =
      match pairs.lookup key with
      | some value => PMF.pure value
      | none => PMF.uniformOfFintype (Fin (2 ^ 256)) := by
  have scanned := hashScan_lookup encode injective pairs key memory oracle represented index operand fits
  have projected := congrArg (PMF.map BitVec.toFin) (hashTailSamples_reply (hashScan pairs.length memory).1)
  rw [scanned] at projected
  cases known : pairs.lookup key with
  | none =>
      rw [known, Option.map_none, hashWord_uniform] at projected
      simpa only [hashHandlerSamples, PMF.map_comp, Function.comp_def] using projected
  | some value =>
      rw [known, Option.map_some, PMF.pure_map, hashWord_toFin] at projected
      simpa only [hashHandlerSamples, PMF.map_comp, Function.comp_def] using projected

/-- The next source table retains known replies and stores fresh replies. -/
def hashNextTable {Key : Type} [DecidableEq Key] (pairs : HashTable Key (2 ^ 256))
    (key : Key) (value : Fin (2 ^ 256)) : HashTable Key (2 ^ 256) :=
  if pairs.lookup key = none then (key, value) :: pairs else pairs

/-- The compiled reply and next finite table have the joint operational source law. -/
theorem hashHandlerSamples_joint {Key : Type} [DecidableEq Key] (encode : Key → Word)
    (injective : Function.Injective encode) (pairs : HashTable Key (2 ^ 256)) (key : Key)
    (memory : Memory) (oracle : Fin 15749)
    (represented : HashMemory memory.ram oracle (hashWordPairs encode pairs))
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = encode key) (fits : 2 * pairs.length ≤ 2 ^ 110) :
    (hashHandlerSamples pairs.length memory).map (fun result =>
      let value := (result.1.registers 8).toFin
      (value, hashNextTable pairs key value)) =
      (pairs.query (by decide) key).distribution := by
  have replies := hashHandlerSamples_finite encode injective pairs key memory oracle represented index operand fits
  have joint := congrArg (PMF.map (fun value => (value, hashNextTable pairs key value))) replies
  rw [PMF.map_comp] at joint
  have source : (match pairs.lookup key with
      | some value => PMF.pure value
      | none => PMF.uniformOfFintype (Fin (2 ^ 256))).map
        (fun value => (value, hashNextTable pairs key value)) =
      (pairs.query (by decide) key).distribution := by
    cases known : pairs.lookup key <;>
      simp [HashTable.query, known, Draw.distribution, hashNextTable, PMF.pure_map]
  simpa only [Function.comp_def] using joint.trans source

end Kriterion.ArgoMAC.ArithmeticSimulator
