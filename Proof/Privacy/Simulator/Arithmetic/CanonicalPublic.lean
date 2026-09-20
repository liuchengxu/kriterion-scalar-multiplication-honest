import Proof.Privacy.Simulator.Arithmetic.EncodingBits

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open GarbledCircuit.SimulatorProtocol

/-- The protocol parser accepts every complete canonical encoding. -/
theorem publicValue_bytes {Public : Type} (encoding : Encoding Public) (value : Public)
    (count : Nat) (length : (encoding.encode value).length = count) :
    publicValue encoding count ((encoding.encode value).flatMap (fun byte => bits 8 byte.val)) = some value := by
  let values : Vector (BitVec 8) count :=
    ⟨((encoding.encode value).map (fun byte => BitVec.ofNat 8 byte.val)).toArray, by simp [length]⟩
  have represented : encoding.encode value = (values.map BitVec.toFin).toList := by
    simp only [values, Vector.toList_map, Vector.toList_mk, List.toList_toArray, List.map_map]
    symm
    have identity : (fun byte : Fin 256 => (BitVec.ofNat 8 byte.val).toFin) = id := by
      funext byte
      apply Fin.ext
      simp [BitVec.toFin, BitVec.toNat_ofNat, Nat.mod_eq_of_lt byte.isLt]
    simp only [Function.comp_def, identity, List.map_id]
  have decoded := publicValue_encoded encoding value count values represented
  have same : values.toList.flatMap (fun byte => bits 8 byte.toNat) =
      (encoding.encode value).flatMap (fun byte => bits 8 byte.val) := by
    simp only [values, Vector.toList_mk, List.toList_toArray, List.flatMap_map, Function.comp_def]
    congr 1
    funext byte
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt byte.isLt]
  rw [same] at decoded
  exact decoded

/-- A checked output projection preserves the parser result. -/
theorem parse_mapped_output {State Output Value : Type} (law : PMF (Option State))
    (project : State → Output) (parser : Output → Option Value) (output : Output) (value : Value)
    (source : law.map (Option.map project) = PMF.pure (some output))
    (accepted : parser output = some value) :
    law.map (fun result => result.bind fun state => parser (project state)) = PMF.pure (some value) := by
  have parsed := congrArg (PMF.map (fun result : Option Output => result.bind parser)) source
  simpa only [PMF.map_comp, Function.comp_def, Option.bind_map, PMF.pure_map,
    Option.bind_some, accepted] using parsed

end Kriterion.ArgoMAC.ArithmeticSimulator
