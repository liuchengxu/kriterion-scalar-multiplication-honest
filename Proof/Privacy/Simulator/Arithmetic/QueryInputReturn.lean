import Proof.Privacy.Simulator.Arithmetic.QueryInputBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol

theorem queryInputBlock_fixedPrefix [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 97 → Fin (host.size + 1)) (present : ContainsQueryInput host labels) (base : Memory)
    (tag index value : Nat) (rest : List Bool) (tagBound : tag < 2)
    (wire : base.bits 0 = bits 3 tag ++ bits 14 index ++ bits 128 value ++ rest) :
    runPrefix host 1041 ⟨labels 0, base⟩ =
      PMF.pure (some (false, ⟨labels 96, fixedQueryMemory base tag index value rest⟩, 1041)) := by
  let tagged := decodedInput base 3 tag (bits 14 index ++ bits 128 value ++ rest)
  let indexed := decodedInput (queryTagState tagged) 14 index (bits 128 value ++ rest)
  let payload := decodedInput (queryFixedState indexed) 128 value rest
  have tagRead := decodedInputHost_prefix host 3 tag (fun pc => labels (queryInputLabels 0 14 pc))
    (queryInputBlock_word host labels present 3 0 14 queryInput_blocks.1) base (bits 14 index ++ bits 128 value ++ rest) wire (by decide)
  change runPrefix host 27 ⟨labels 0, base⟩ = PMF.pure (some (false, ⟨labels 14, tagged⟩, 27)) at tagRead
  have tagValue : (tagged.registers 0).toNat = tag := by
    rw [decodedInput_value base 3 tag _ (by omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans tagBound (by decide : 2 < 2 ^ 256))]
  have branch := queryInputBlock_tag host labels present tagged
  rw [tagValue, if_pos tagBound] at branch
  have indexRead := decodedInputHost_prefix host 14 index (fun pc => labels (queryInputLabels 19 33 pc))
    (queryInputBlock_word host labels present 14 19 33 queryInput_blocks.2.1) (queryTagState tagged) (bits 128 value ++ rest) rfl (by decide)
  change runPrefix host 104 ⟨labels 19, queryTagState tagged⟩ =
    PMF.pure (some (false, ⟨labels 33, indexed⟩, 104)) at indexRead
  have payloadRead := decodedInputHost_prefix host 128 value (fun pc => labels (queryInputLabels 80 94 pc))
    (queryInputBlock_word host labels present 128 80 94 queryInput_blocks.2.2.2.2) (queryFixedState indexed) rest rfl (by decide)
  change runPrefix host 902 ⟨labels 80, queryFixedState indexed⟩ =
    PMF.pure (some (false, ⟨labels 94, payload⟩, 902)) at payloadRead
  change runPrefix host (27 + (5 + (104 + (2 + (902 + 1))))) ⟨labels 0, base⟩ = _
  rw [prefix_add, tagRead, PMF.pure_bind]
  dsimp only
  rw [prefix_add, branch, PMF.pure_bind]
  dsimp only
  rw [prefix_add, indexRead, PMF.pure_bind]
  dsimp only
  rw [prefix_add, queryInputBlock_fixedIndex host labels present, PMF.pure_bind]
  dsimp only
  rw [prefix_add, payloadRead, PMF.pure_bind]
  dsimp only
  simp [runPrefix, step, present 94 (by decide), relocate, queryInput, queryOperandState, Arithmetic.eval,
    PMF.pure_map, fixedQueryMemory, tagged, indexed, payload]
  all_goals rfl


theorem queryInputBlock_encPrefix [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 97 → Fin (host.size + 1)) (present : ContainsQueryInput host labels) (base : Memory)
    (tag index value : Nat) (rest : List Bool) (tagLower : 2 ≤ tag) (tagBound : tag < 4)
    (wire : base.bits 0 = bits 3 tag ++ bits 9 index ++ bits 128 value ++ rest) :
    runPrefix host 1010 ⟨labels 0, base⟩ =
      PMF.pure (some (false, ⟨labels 96, encQueryMemory base tag index value rest⟩, 1010)) := by
  let tagged := decodedInput base 3 tag (bits 9 index ++ bits 128 value ++ rest)
  let indexed := decodedInput (queryFamilyState (queryTagState tagged)) 9 index (bits 128 value ++ rest)
  let payload := decodedInput (queryEncState indexed) 128 value rest
  have tagRead := decodedInputHost_prefix host 3 tag (fun pc => labels (queryInputLabels 0 14 pc))
    (queryInputBlock_word host labels present 3 0 14 queryInput_blocks.1) base (bits 9 index ++ bits 128 value ++ rest) wire (by decide)
  change runPrefix host 27 ⟨labels 0, base⟩ = PMF.pure (some (false, ⟨labels 14, tagged⟩, 27)) at tagRead
  have tagValue : (tagged.registers 0).toNat = tag := by
    rw [decodedInput_value base 3 tag _ (by omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans tagBound (by decide : 4 < 2 ^ 256))]
  have branch := queryInputBlock_tag host labels present tagged
  rw [tagValue, if_neg (Nat.not_lt.mpr tagLower)] at branch
  have family := queryInputBlock_family host labels present (queryTagState tagged)
  have familyValue : ((queryTagState tagged).registers 10).toNat = tag := by
    simpa [queryTagState] using tagValue
  rw [familyValue, if_pos tagBound] at family
  have indexRead := decodedInputHost_prefix host 9 index (fun pc => labels (queryInputLabels 38 52 pc))
    (queryInputBlock_word host labels present 9 38 52 queryInput_blocks.2.2.1) (queryFamilyState (queryTagState tagged)) (bits 128 value ++ rest) rfl (by decide)
  change runPrefix host 69 ⟨labels 38, queryFamilyState (queryTagState tagged)⟩ =
    PMF.pure (some (false, ⟨labels 52, indexed⟩, 69)) at indexRead
  have payloadRead := decodedInputHost_prefix host 128 value (fun pc => labels (queryInputLabels 80 94 pc))
    (queryInputBlock_word host labels present 128 80 94 queryInput_blocks.2.2.2.2) (queryEncState indexed) rest rfl (by decide)
  change runPrefix host 902 ⟨labels 80, queryEncState indexed⟩ =
    PMF.pure (some (false, ⟨labels 94, payload⟩, 902)) at payloadRead
  change runPrefix host (27 + (5 + (3 + (69 + (3 + (902 + 1)))))) ⟨labels 0, base⟩ = _
  rw [prefix_add, tagRead, PMF.pure_bind]
  dsimp only
  rw [prefix_add, branch, PMF.pure_bind]
  dsimp only
  rw [prefix_add, family, PMF.pure_bind]
  dsimp only
  rw [prefix_add, indexRead, PMF.pure_bind]
  dsimp only
  rw [prefix_add, queryInputBlock_encIndex host labels present, PMF.pure_bind]
  dsimp only
  rw [prefix_add, payloadRead, PMF.pure_bind]
  dsimp only
  simp [runPrefix, step, present 94 (by decide), relocate, queryInput, queryOperandState, Arithmetic.eval,
    PMF.pure_map, encQueryMemory, tagged, indexed, payload]
  all_goals rfl


theorem queryInputBlock_hashPrefix [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 97 → Fin (host.size + 1)) (present : ContainsQueryInput host labels) (base : Memory)
    (value : Nat) (rest : List Bool)
    (wire : base.bits 0 = bits 3 4 ++ bits 254 value ++ rest) :
    runPrefix host 1821 ⟨labels 0, base⟩ =
      PMF.pure (some (false, ⟨labels 96, hashQueryMemory base value rest⟩, 1821)) := by
  let tagged := decodedInput base 3 4 (bits 254 value ++ rest)
  let selected := queryHashState (queryFamilyState (queryTagState tagged))
  let payload := decodedInput selected 254 value rest
  have tagRead := decodedInputHost_prefix host 3 4 (fun pc => labels (queryInputLabels 0 14 pc))
    (queryInputBlock_word host labels present 3 0 14 queryInput_blocks.1) base (bits 254 value ++ rest) wire (by decide)
  change runPrefix host 27 ⟨labels 0, base⟩ = PMF.pure (some (false, ⟨labels 14, tagged⟩, 27)) at tagRead
  have tagValue : (tagged.registers 0).toNat = 4 := by
    rw [decodedInput_value base 3 4 _ (by decide)]
    rfl
  have branch := queryInputBlock_tag host labels present tagged
  simp only [tagValue, show ¬ 4 < 2 by decide, if_false] at branch
  have family := queryInputBlock_family host labels present (queryTagState tagged)
  have familyValue : ((queryTagState tagged).registers 10).toNat = 4 := by
    simpa [queryTagState] using tagValue
  simp only [familyValue, lt_self_iff_false, if_false] at family
  have select : runPrefix host 1 ⟨labels 56, queryFamilyState (queryTagState tagged)⟩ =
      PMF.pure (some (false, ⟨labels 57, selected⟩, 1)) := by
    simp [runPrefix, step, present 56 (by decide), relocate, queryInput, selected, queryHashState, PMF.pure_map]
  have payloadRead := decodedInputHost_prefix host 254 value (fun pc => labels (queryInputLabels 57 71 pc))
    (queryInputBlock_word host labels present 254 57 71 queryInput_blocks.2.2.2.1) selected rest rfl (by decide)
  change runPrefix host 1784 ⟨labels 57, selected⟩ =
    PMF.pure (some (false, ⟨labels 71, payload⟩, 1784)) at payloadRead
  change runPrefix host (27 + (5 + (3 + (1 + (1784 + 1))))) ⟨labels 0, base⟩ = _
  rw [prefix_add, tagRead, PMF.pure_bind]
  dsimp only
  rw [prefix_add, branch, PMF.pure_bind]
  dsimp only
  rw [prefix_add, family, PMF.pure_bind]
  dsimp only
  rw [prefix_add, select, PMF.pure_bind]
  dsimp only
  rw [prefix_add, payloadRead, PMF.pure_bind]
  dsimp only
  simp [runPrefix, step, present 71 (by decide), relocate, queryInput, queryOperandState, Arithmetic.eval,
    PMF.pure_map, hashQueryMemory, tagged, selected, payload]
  all_goals rfl

/-- The return memory uses the source state for the selected query family. -/
noncomputable def queryInputMemory (base : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) : Memory :=
  match request with
  | .fixedForward index value => fixedQueryMemory base 0
      (Fintype.equivFin Shared.FixedKeyIndex index).val value.toNat rest
  | .fixedInverse index value => fixedQueryMemory base 1
      (Fintype.equivFin Shared.FixedKeyIndex index).val value.toNat rest
  | .encForward index value => encQueryMemory base 2
      (Fintype.equivFin EncPRF.PermutationIndex index).val value.toNat rest
  | .encInverse index value => encQueryMemory base 3
      (Fintype.equivFin EncPRF.PermutationIndex index).val value.toNat rest
  | .hash value => hashQueryMemory base value.val rest

/-- Every public query returns to the caller before the final reader halt. -/
theorem queryInputBlock_prefix [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 97 → Fin (host.size + 1)) (present : ContainsQueryInput host labels)
    (base : Memory) (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (rest : List Bool) (wire : base.bits 0 = query request ++ rest) :
    runPrefix host (queryInputCost request - 1) ⟨labels 0, base⟩ =
      PMF.pure (some (false, ⟨labels 96, queryInputMemory base request rest⟩,
        queryInputCost request - 1)) := by
  cases request with
  | fixedForward index value =>
      simpa only [queryInputCost, queryInputMemory, Nat.reduceSub] using
        queryInputBlock_fixedPrefix host labels present base 0
          (Fintype.equivFin Shared.FixedKeyIndex index).val value.toNat rest (by decide)
          (by simpa only [GarbledCircuit.SimulatorProtocol.query, sharedFixedKeyIndex_count, fixedIndexWidth, List.append_assoc] using wire)
  | fixedInverse index value =>
      simpa only [queryInputCost, queryInputMemory, Nat.reduceSub] using
        queryInputBlock_fixedPrefix host labels present base 1
          (Fintype.equivFin Shared.FixedKeyIndex index).val value.toNat rest (by decide)
          (by simpa only [GarbledCircuit.SimulatorProtocol.query, sharedFixedKeyIndex_count, fixedIndexWidth, List.append_assoc] using wire)
  | encForward index value =>
      simpa only [queryInputCost, queryInputMemory, Nat.reduceSub] using
        queryInputBlock_encPrefix host labels present base 2
          (Fintype.equivFin EncPRF.PermutationIndex index).val value.toNat rest (by decide) (by decide)
          (by simpa only [GarbledCircuit.SimulatorProtocol.query, encPermutationIndex_count, encIndexWidth, List.append_assoc] using wire)
  | encInverse index value =>
      simpa only [queryInputCost, queryInputMemory, Nat.reduceSub] using
        queryInputBlock_encPrefix host labels present base 3
          (Fintype.equivFin EncPRF.PermutationIndex index).val value.toNat rest (by decide) (by decide)
          (by simpa only [GarbledCircuit.SimulatorProtocol.query, encPermutationIndex_count, encIndexWidth, List.append_assoc] using wire)
  | hash value =>
      simpa only [queryInputCost, queryInputMemory, Nat.reduceSub] using
        queryInputBlock_hashPrefix host labels present base value.val rest
          (by simpa only [GarbledCircuit.SimulatorProtocol.query, List.append_assoc] using wire)

/-- The query reader passes its complete memory and exact cost to the caller. -/
theorem queryInputBlock_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 97 → Fin (host.size + 1)) (present : ContainsQueryInput host labels)
    (base : Memory) (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (rest : List Bool) (wire : base.bits 0 = query request ++ rest) (fuel : Nat) :
    run host (queryInputCost request - 1 + fuel) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels 96, queryInputMemory base request rest⟩).map
        (Option.map fun result => (result.1, result.2 + (queryInputCost request - 1))) := by
  rw [run_after_prefix, queryInputBlock_prefix host labels present base request rest wire,
    PMF.pure_bind]

/-- The caller receives the parsed query and unchanged permanent RAM. -/
theorem queryInputMemory_values (base : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) :
    let result := queryInputMemory base request rest
    result.registers 8 = (queryOperands request).1 ∧
    result.registers 9 = (queryOperands request).2.1 ∧
    result.registers 10 = (queryOperands request).2.2 ∧
    result.bits 0 = rest ∧ result.ram = base.ram := by
  cases request with
  | fixedForward index value =>
      have indexBound : (Fintype.equivFin Shared.FixedKeyIndex index).val < 15240 := by
        simpa only [sharedFixedKeyIndex_count] using (Fintype.equivFin Shared.FixedKeyIndex index).isLt
      simpa only [queryInputMemory, queryOperands] using fixedQueryMemory_values base 0
        (Fintype.equivFin Shared.FixedKeyIndex index).val value.toNat rest (by decide) indexBound value.isLt
  | fixedInverse index value =>
      have indexBound : (Fintype.equivFin Shared.FixedKeyIndex index).val < 15240 := by
        simpa only [sharedFixedKeyIndex_count] using (Fintype.equivFin Shared.FixedKeyIndex index).isLt
      simpa only [queryInputMemory, queryOperands] using fixedQueryMemory_values base 1
        (Fintype.equivFin Shared.FixedKeyIndex index).val value.toNat rest (by decide) indexBound value.isLt
  | encForward index value =>
      have indexBound : (Fintype.equivFin EncPRF.PermutationIndex index).val < 508 := by
        simpa only [encPermutationIndex_count] using (Fintype.equivFin EncPRF.PermutationIndex index).isLt
      simpa only [queryInputMemory, queryOperands] using encQueryMemory_values base 2
        (Fintype.equivFin EncPRF.PermutationIndex index).val value.toNat rest (by decide) indexBound value.isLt
  | encInverse index value =>
      have indexBound : (Fintype.equivFin EncPRF.PermutationIndex index).val < 508 := by
        simpa only [encPermutationIndex_count] using (Fintype.equivFin EncPRF.PermutationIndex index).isLt
      simpa only [queryInputMemory, queryOperands] using encQueryMemory_values base 3
        (Fintype.equivFin EncPRF.PermutationIndex index).val value.toNat rest (by decide) indexBound value.isLt
  | hash value =>
      simpa only [queryInputMemory, queryOperands] using hashQueryMemory_values base value.val rest
        (lt_trans value.val_lt (by decide : BN254.baseFieldModulus < 2 ^ 254))

end Kriterion.ArgoMAC.ArithmeticSimulator
