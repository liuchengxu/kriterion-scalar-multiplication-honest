import Proof.Privacy.Simulator.Arithmetic.HashSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The hash scan flag identifies exactly the fresh source keys. -/
theorem hashScan_fresh {Key : Type} [DecidableEq Key] (encode : Key → Word)
    (injective : Function.Injective encode) (pairs : HashTable Key (2 ^ 256)) (key : Key)
    (memory : Memory) (oracle : Fin 15749)
    (represented : HashMemory memory.ram oracle (hashWordPairs encode pairs))
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = encode key) (fits : 2 * pairs.length ≤ 2 ^ 110) :
    (hashScan pairs.length memory).1.registers 12 = 0#256 ↔ pairs.lookup key = none := by
  have lookup := hashScan_lookup encode injective pairs key memory oracle represented index operand fits
  change (if (hashScan pairs.length memory).1.registers 12 = 0#256 then none
    else some ((hashScan pairs.length memory).1.registers 11)) = _ at lookup
  by_cases fresh : (hashScan pairs.length memory).1.registers 12 = 0#256
  · rw [if_pos fresh] at lookup
    cases known : pairs.lookup key with
    | none => exact ⟨fun _ => rfl, fun _ => fresh⟩
    | some value => simp [known] at lookup
  · rw [if_neg fresh] at lookup
    cases known : pairs.lookup key with
    | none => simp [known] at lookup
    | some value => simp [fresh]

/-- The complete hash source retains the RAM representation of its next finite table. -/
theorem hashHandlerSamples_memory {Key : Type} [DecidableEq Key] (encode : Key → Word)
    (injective : Function.Injective encode) (pairs : HashTable Key (2 ^ 256)) (key : Key)
    (memory final : Memory) (cost : Nat) (oracle : Fin 15749)
    (represented : HashMemory memory.ram oracle (hashWordPairs encode pairs))
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = encode key) (fits : 2 * (pairs.length + 1) + 256 < 2 ^ 110)
    (supported : (final, cost) ∈ (hashHandlerSamples pairs.length memory).support) :
    HashMemory final.ram oracle
      (hashWordPairs encode (hashNextTable pairs key (final.registers 8).toFin)) := by
  have length : (hashWordPairs encode pairs).length = pairs.length := by simp [hashWordPairs]
  have capacity : 2 * pairs.length ≤ 2 ^ 110 := by omega
  have loaded := HashMemory.loaded memory oracle (hashWordPairs encode pairs) represented (by simpa only [length] using capacity)
  have frame := hashScan_frame pairs.length memory
  have scanMemory : HashMemory (hashScan pairs.length memory).1.ram oracle (hashWordPairs encode pairs) := by
    rw [frame.1]
    exact loaded
  have scanBase : (hashScan pairs.length memory).1.registers 5 =
      oracleAddress oracle 0 (2 ^ 110 - 2 * (hashWordPairs encode pairs).length) := by
    rw [frame.2.2.2.1, length]
    exact oracleLoaded_inputBase memory oracle pairs.length index (by simpa only [length] using represented.count) capacity
  have scanCount : (hashScan pairs.length memory).1.registers 0 = BitVec.ofNat 256 (hashWordPairs encode pairs).length :=
    frame.2.1.trans ((oracleLoaded_used memory oracle index).trans represented.count)
  have scanBackup : (hashScan pairs.length memory).1.registers 4 = BitVec.ofNat 256 (hashWordPairs encode pairs).length := by
    rw [frame.2.2.1]
    have same : (oracleLoaded memory).registers 4 = (oracleLoaded memory).registers 0 := by simp [oracleLoaded]
    exact same.trans ((oracleLoaded_used memory oracle index).trans represented.count)
  have scanHeader : (hashScan pairs.length memory).1.ram 13 = oracleAddress oracle 0 0 := by
    rw [frame.1, (oracleLoaded_query memory).2.2.2, index, oracleHeader_address]
  unfold hashHandlerSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have stored := hashTailSamples_memory (hashScan pairs.length memory).1 before spent oracle
    (hashWordPairs encode pairs) scanMemory scanBase scanCount scanBackup scanHeader
    (by simpa only [length] using fits) member
  have scanKey := frame.2.2.2.2.trans ((oracleLoaded_query memory).1.trans operand)
  have fresh := hashScan_fresh encode injective pairs key memory oracle represented index operand capacity
  by_cases absent : pairs.lookup key = none
  · rw [if_pos (fresh.mpr absent), scanKey] at stored
    simpa [hashNextTable, absent, hashWordPairs] using stored
  · rw [if_neg (fun zero => absent (fresh.mp zero))] at stored
    simpa only [hashNextTable, if_neg absent] using stored

end Kriterion.ArgoMAC.ArithmeticSimulator
