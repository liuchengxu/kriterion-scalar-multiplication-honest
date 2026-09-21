import Construction.SharedGarbling

namespace Kriterion.ArgoMAC.Shared
open BN254 Cryptography

abbrev Program (Result : Type) (budget : Nat) :=
  QueryProgram (publicOracleSpec FixedKeyIndex EncPRF.PermutationIndex) Result budget

/-- Each cached gate contains only the answers that this run requested.
Decryption reads the transmitted payload, so it masks the pad first. -/
def cachedGate (hash : BaseField) (pad : BitVec 256) : BitAdaptor.FixedKeyOracle where
  hashToField _ := hash
  encrypt _ message := pad ^^^ BitAdaptor.fieldBytes message
  decrypt _ row := (BitAdaptor.payload pad ^^^ row).toNat
  decryptEncrypt _ message := by
    simp only [BitAdaptor.payload, BitVec.setWidth_xor]
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    simp only [BitAdaptor.fieldBytes, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by decide : coordinateBitCount ≤ 256)),
      Nat.mod_eq_of_lt]
    · exact ZMod.natCast_zmod_val message
    · exact lt_trans message.val_lt (by decide)

def gateIndex (location : Pipeline.FixedKeyLocation) (position : Fin coordinateBitCount)
    (slot : Fin 3) : FixedKeyIndex := ⟨location.kind, position, slot⟩

/-- Garbling requests three hash blocks and two pad blocks. -/
def garbleGate (location : Pipeline.FixedKeyLocation) (position : Fin coordinateBitCount)
    (key : BitAdaptor.Key) : Program BitAdaptor.FixedKeyOracle 5 :=
  let zero := key.falseLabel ^^^ location.tweak
  let one := key.trueLabel ^^^ location.tweak
  .query (.fixedForward (gateIndex location position 0) zero) fun (z0 : Block) =>
  .query (.fixedForward (gateIndex location position 1) zero) fun (z1 : Block) =>
  .query (.fixedForward (gateIndex location position 2) zero) fun (z2 : Block) =>
  .query (.fixedForward (gateIndex location position 0) one) fun (o0 : Block) =>
  .query (.fixedForward (gateIndex location position 1) one) fun (o1 : Block) =>
  .pure (cachedGate (((z2 ^^^ zero) ++ (z1 ^^^ zero) ++ (z0 ^^^ zero)).toNat)
    ((o1 ^^^ one) ++ (o0 ^^^ one)))

/-- Evaluation reuses the first two hash slots for the pad. -/
def evaluateGate (location : Pipeline.FixedKeyLocation) (position : Fin coordinateBitCount)
    (label : Block) : Program BitAdaptor.FixedKeyOracle 3 :=
  let input := label ^^^ location.tweak
  .query (.fixedForward (gateIndex location position 0) input) fun (p0 : Block) =>
  .query (.fixedForward (gateIndex location position 1) input) fun (p1 : Block) =>
  .query (.fixedForward (gateIndex location position 2) input) fun (p2 : Block) =>
  .pure (cachedGate (((p2 ^^^ input) ++ (p1 ^^^ input) ++ (p0 ^^^ input)).toNat)
    ((p1 ^^^ input) ++ (p0 ^^^ input)))

theorem garbleGate_correct (oracle : PublicOracle FixedKeyIndex EncPRF.PermutationIndex)
    (location : Pipeline.FixedKeyLocation) (position : Fin coordinateBitCount)
    (key : BitAdaptor.Key) (slope : BaseField) :
    BitAdaptor.garble ((garbleGate location position key).eval (publicAnswer oracle)) slope key =
      BitAdaptor.garble (Pipeline.fixedKeyGate (expandOracle oracle.1) location position.val)
        slope key := by
  simp only [garbleGate, QueryProgram.eval, publicAnswer, cachedGate, BitAdaptor.garble,
    BitAdaptor.OutputKey.encode, Pipeline.fixedKeyGate, BitAdaptor.fixedKeyOracle,
    BitAdaptor.hashBytes, BitAdaptor.padBytes, Pipeline.fixedKeyPermutations,
    expandOracle, fixedIndex, slotIndex, gateIndex, daviesMeyer, Cryptography.xor, Nat.mod_eq_of_lt position.isLt]
  all_goals rfl

theorem evaluateGate_correct (oracle : PublicOracle FixedKeyIndex EncPRF.PermutationIndex)
    (location : Pipeline.FixedKeyLocation) (position : Fin coordinateBitCount)
    (label : Block) (table : BitAdaptor.Table) (value : Bool) :
    BitAdaptor.evaluate ((evaluateGate location position label).eval (publicAnswer oracle))
      table value label =
      BitAdaptor.evaluate (Pipeline.fixedKeyGate (expandOracle oracle.1) location position.val)
        table value label := by
  cases value <;> simp only [evaluateGate, QueryProgram.eval, publicAnswer, cachedGate,
    BitAdaptor.evaluate, Bool.false_eq_true, ↓reduceIte, Pipeline.fixedKeyGate,
    BitAdaptor.fixedKeyOracle, BitAdaptor.hashBytes, BitAdaptor.padBytes,
    Pipeline.fixedKeyPermutations, expandOracle, fixedIndex, slotIndex, gateIndex,
    daviesMeyer, Cryptography.xor, Nat.mod_eq_of_lt position.isLt]
  all_goals rfl

def curveLocation : Fin 5 → Pipeline.FixedKeyLocation
  | 0 => .curve .y4 | 1 => .curve .y6 | 2 => .curve .x3
  | 3 => .curve .x5 | 4 => .curve .x7

def pointCoordinate : Fin 3 → Pipeline.PointCoordinate
  | 0 => .x | 1 => .y | 2 => .z

def pointAdaptor : Fin 5 → Pipeline.PointAdaptor
  | 0 => .y6 | 1 => .y8 | 2 => .y10 | 3 => .x7 | 4 => .x9

def curveOraclesFrom (gates : Vector (Vector BitAdaptor.FixedKeyOracle coordinateBitCount) 5) :
    CurveMembership.Oracles :=
  let get (which : Fin 5) (index : Nat) := gates[which].get ⟨index % coordinateBitCount, Nat.mod_lt _ (by decide)⟩
  ⟨get 0, get 1, get 2, get 3, get 4⟩

def pointOraclesFrom (gates : Vector (Vector (Vector
    (Vector BitAdaptor.FixedKeyOracle coordinateBitCount) 5) 3) FieldMacToECMac.outputMacCount) :
    FieldMacToECMac.Oracles :=
  Vector.ofFn fun output =>
    let get (coordinate : Fin 3) : Biquadratic.Oracles :=
      let window (which : Fin 5) (index : Nat) := gates[output][coordinate][which].get ⟨index % coordinateBitCount, Nat.mod_lt _ (by decide)⟩
      ⟨window 0, window 1, window 2, window 3, window 4⟩
    ⟨get 0, get 1, get 2⟩

def curveGates {budget : Nat}
    (gate : Pipeline.FixedKeyLocation → Fin coordinateBitCount → Program BitAdaptor.FixedKeyOracle budget) :
    Program CurveMembership.Oracles (5 * (254 * budget)) :=
  (QueryProgram.ofFn 5 fun which => QueryProgram.ofFn coordinateBitCount fun position =>
    gate (curveLocation which) position).map curveOraclesFrom

def pointGates {budget : Nat}
    (gate : Pipeline.FixedKeyLocation → Fin coordinateBitCount → Program BitAdaptor.FixedKeyOracle budget) :
    Program FieldMacToECMac.Oracles
      (FieldMacToECMac.outputMacCount * (3 * (5 * (coordinateBitCount * budget)))) :=
  (QueryProgram.ofFn FieldMacToECMac.outputMacCount fun output =>
    QueryProgram.ofFn 3 fun coordinate => QueryProgram.ofFn 5 fun which =>
      QueryProgram.ofFn coordinateBitCount fun position =>
        gate (.point output (pointCoordinate coordinate) (pointAdaptor which)) position).map pointOraclesFrom

/-- Which input coordinate each gate reads. The three-adaptor Y row rebinds
`y ^ 2` to `x ^ 3 + 3`, so every adaptor it keeps reads the x coordinate; it
dropped the `y8` and `y10` adaptors, and no row reads those two locations. -/
def locationKey (input : InputMacKey) : Pipeline.FixedKeyLocation → CoordinateMacKey
  | .curve .y4 | .curve .y6 => input.y
  | .point _ .y _ => input.x
  | .point _ _ .y6 | .point _ _ .y8 | .point _ _ .y10 => input.y
  | _ => input.x

def locationMac (input : InputMac) : Pipeline.FixedKeyLocation → CoordinateMac
  | .curve .y4 | .curve .y6 => input.y
  | .point _ .y _ => input.x
  | .point _ _ .y6 | .point _ _ .y8 | .point _ _ .y10 => input.y
  | _ => input.x

@[simp] theorem position_mod (index : Fin coordinateBitCount) :
    index.val % coordinateBitCount = index.val := Nat.mod_eq_of_lt index.isLt

theorem curveGarble_correct (oracle : PublicOracle FixedKeyIndex EncPRF.PermutationIndex)
    (input : InputMacKey) (bridge mask r1 r2 : BaseField) :
    CurveMembership.garble bridge mask r1 r2
      ((curveGates fun location position => garbleGate location position
        ((locationKey input location).get position)).eval (publicAnswer oracle)) input =
      CurveMembership.garble bridge mask r1 r2 (Pipeline.curveOracles (expandOracle oracle.1)) input := by
  simp only [curveGates, QueryProgram.eval_map, QueryProgram.eval_ofFn, curveOraclesFrom,
    CurveMembership.garble, DigitAdaptor.garble, Fin.getElem_fin, Vector.get_ofFn, Vector.getElem_ofFn,
    position_mod, curveLocation, locationKey, Pipeline.curveOracles, garbleGate_correct]

theorem pointGarble_correct (oracle : PublicOracle FixedKeyIndex EncPRF.PermutationIndex)
    (input : InputMacKey) (rows : FieldMacToECMac.Rows) (randomness : FieldMacToECMac.Randomness) :
    FieldMacToECMac.garble rows randomness
      ((pointGates fun location position => garbleGate location position
        ((locationKey input location).get position)).eval (publicAnswer oracle)) input =
      FieldMacToECMac.garble rows randomness (Pipeline.pointOracles (expandOracle oracle.1)) input := by
  simp only [pointGates, QueryProgram.eval_map, QueryProgram.eval_ofFn, pointOraclesFrom,
    FieldMacToECMac.garble, FieldMacToECMac.garbleRow,
    Biquadratic.garbleX, Biquadratic.garbleY, Biquadratic.garbleZ,
    DigitAdaptor.garble, Fin.getElem_fin, Vector.get_ofFn, Vector.getElem_ofFn,
    position_mod, pointCoordinate, pointAdaptor, locationKey,
    Pipeline.pointOracles, Pipeline.biquadraticOracles, garbleGate_correct]

theorem curveEvaluate_correct (oracle : PublicOracle FixedKeyIndex EncPRF.PermutationIndex)
    (input : InputMac) (table : CurveMembership.Table) (affine : AffineInput) :
    CurveMembership.evaluate
      ((curveGates fun location position => evaluateGate location position
        ((locationMac input location).get position)).eval (publicAnswer oracle)) table affine input =
      CurveMembership.evaluate (Pipeline.curveOracles (expandOracle oracle.1)) table affine input := by
  simp only [curveGates, QueryProgram.eval_map, QueryProgram.eval_ofFn, curveOraclesFrom,
    CurveMembership.evaluate, CurveMembership.evaluateDigit, DigitAdaptor.evaluate,
    Fin.getElem_fin, Vector.get_ofFn, Vector.getElem_ofFn,
    position_mod, curveLocation, locationMac, Pipeline.curveOracles, evaluateGate_correct]

theorem pointEvaluate_correct (oracle : PublicOracle FixedKeyIndex EncPRF.PermutationIndex)
    (input : InputMac) (table : FieldMacToECMac.Table) (affine : AffineInput) :
    FieldMacToECMac.evaluate table
      ((pointGates fun location position => evaluateGate location position
        ((locationMac input location).get position)).eval (publicAnswer oracle)) affine input =
      FieldMacToECMac.evaluate table (Pipeline.pointOracles (expandOracle oracle.1)) affine input := by
  have digit (location : Pipeline.FixedKeyLocation) (labels : CoordinateMac)
      (rows : Option (Vector BitAdaptor.Table coordinateBitCount)) (value : BaseField) :
      Biquadratic.evaluateDigit
        (fun index => (evaluateGate location ⟨index % coordinateBitCount, Nat.mod_lt _ (by decide)⟩
          (labels.get ⟨index % coordinateBitCount, Nat.mod_lt _ (by decide)⟩)).eval (publicAnswer oracle))
        rows value labels =
      Biquadratic.evaluateDigit (Pipeline.fixedKeyGate (expandOracle oracle.1) location) rows value labels := by
    cases rows <;> simp only [Biquadratic.evaluateDigit, DigitAdaptor.evaluate,
      Vector.get_ofFn, position_mod, evaluateGate_correct]
  simp only [pointGates, QueryProgram.eval_map, QueryProgram.eval_ofFn, pointOraclesFrom,
    FieldMacToECMac.evaluate, FieldMacToECMac.evaluateHomogeneous,
    Biquadratic.evaluate, Biquadratic.evaluateY, Fin.getElem_fin, Vector.get_ofFn, Vector.getElem_ofFn,
    pointCoordinate, pointAdaptor, locationMac,
    Pipeline.pointOracles, Pipeline.biquadraticOracles, digit]

def transformLabel (keys : WhiteningKeys) (coordinate : EncPRF.Coordinate)
    (position : Fin coordinateBitCount) (bit : Bool) (label : Block) : Program Block 1 :=
  .query (.encForward (coordinate, position) (encodeBit bit ^^^ keys.first)) fun (answer : Block) =>
    .pure ((answer ^^^ keys.second) ^^^ label)

def transformKey (keys : WhiteningKeys) (input : InputMacKey) : Program InputMacKey 1016 :=
  let coordinate (which : EncPRF.Coordinate) (key : CoordinateMacKey) :=
    QueryProgram.ofFn coordinateBitCount fun position =>
      (transformLabel keys which position false (key.get position).falseLabel).bind fun zero =>
      (transformLabel keys which position true (key.get position).trueLabel).map fun one =>
        (⟨zero, one⟩ : BitAdaptor.Key)
  (coordinate .x input.x).bind fun x => (coordinate .y input.y).map fun y => ⟨x, y⟩

def transformMac (keys : WhiteningKeys) (input : BitInput) (mac : InputMac) : Program InputMac 508 :=
  let coordinate (which : EncPRF.Coordinate) (bits : BitVec coordinateBitCount) (labels : CoordinateMac) :=
    QueryProgram.ofFn coordinateBitCount fun position =>
      transformLabel keys which position (bits.getLsb position) (labels.get position)
  (coordinate .x input.xBits mac.x).bind fun x => (coordinate .y input.yBits mac.y).map fun y => ⟨x, y⟩

theorem transformKey_correct (oracle : PublicOracle FixedKeyIndex EncPRF.PermutationIndex)
    (keys : WhiteningKeys) (input : InputMacKey) :
    (transformKey keys input).eval (publicAnswer oracle) = EncPRF.transformKey oracle.2.1 keys input := by
  simp only [transformKey, QueryProgram.eval_bind, QueryProgram.eval_map, QueryProgram.eval_ofFn,
    transformLabel, QueryProgram.eval, publicAnswer, EncPRF.transformKey,
    EncPRF.transformCoordinateKey, EncPRF.transformAt, EncPRF.evenMansourPad,
    evenMansour, encrypt, Cryptography.xor]
  rfl

theorem transformMac_correct (oracle : PublicOracle FixedKeyIndex EncPRF.PermutationIndex)
    (keys : WhiteningKeys) (input : BitInput) (mac : InputMac) :
    (transformMac keys input mac).eval (publicAnswer oracle) = EncPRF.transformMac oracle.2.1 keys input mac := by
  simp only [transformMac, QueryProgram.eval_bind, QueryProgram.eval_map, QueryProgram.eval_ofFn,
    transformLabel, QueryProgram.eval, publicAnswer, EncPRF.transformMac,
    EncPRF.transformCoordinateMac, EncPRF.transformAt, EncPRF.evenMansourPad,
    evenMansour, encrypt, Cryptography.xor]
  rfl

/-- One hash query, the `1016` transform queries, the five curve adaptors at
254 positions with five queries each, and one five-query gate for every point
coordinate, window and position of every transmitted row. -/
def garbleQueries : Nat := 1740917

/-- Three curve-adaptor queries per position, one hash query, the `508`
transform queries, and three queries per point gate. -/
def evaluateQueries : Nat := 1044449

/-- This program requests all gate answers before it constructs the table. -/
def garbleProgram [FieldCertificate] [GroupCertificate] (_parameter : Nat)
    (scalar : NonZeroScalar) (coins : PrivateCoins) : Program (Pipeline.Table × InputMacKey) garbleQueries :=
  let tape := coins.val.val
  .query (.hash tape.bridgeKey) fun (hash : Block × Block) =>
    (transformKey ⟨hash.1, hash.2⟩ tape.inputMacKey).bind fun transformed =>
    (curveGates fun location position => garbleGate location position
      ((locationKey tape.inputMacKey location).get position)).bind fun curve =>
    (pointGates fun location position => garbleGate location position
      ((locationKey transformed location).get position)).map fun point =>
    (⟨CurveMembership.garble tape.bridgeKey tape.curveMask.value tape.curveR1 tape.curveR2 curve tape.inputMacKey,
      FieldMacToECMac.garble (FieldMacToECMac.rowsForOutputKeys
        (FieldMacToECMac.outputKeys construction scalar.value tape.offsets) tape.pointRandomness)
        tape.pointRandomness point transformed⟩, tape.inputMacKey)

/-- The evaluator requests only public oracle answers and selected labels. -/
def evaluateProgram [FieldCertificate] [GroupCertificate] (table : Pipeline.Table)
    (input : AffineInput) (labels : GarbledCircuit.LamportSignature) :
    Program (Option (Option Point)) evaluateQueries :=
  let restored := Lamport.restore input labels
  match decodePoint restored.input.toAffine with
  | none => .pure (some none)
  | some _ =>
    (curveGates fun location position => evaluateGate location position
      ((locationMac restored.inputMac location).get position)).bind fun curve =>
    QueryProgram.query (oracle := publicOracleSpec FixedKeyIndex EncPRF.PermutationIndex)
      (.hash (CurveMembership.evaluate curve table.curve restored.input.toAffine restored.inputMac))
      fun (hash : Block × Block) =>
    (transformMac ⟨hash.1, hash.2⟩ restored.input restored.inputMac).bind fun transformed =>
    (pointGates fun location position => evaluateGate location position
      ((locationMac transformed location).get position)).map fun point =>
    some (Garbling.decodeResult (FieldMacToECMac.evaluate table.pointMAC point restored.input.toAffine transformed))

set_option backward.isDefEq.respectTransparency false in
theorem garbleProgram_correct [FieldCertificate] [GroupCertificate]
    (parameter : Nat) (scalar : NonZeroScalar) (coins : PrivateCoins)
    (oracle : PublicOracle FixedKeyIndex EncPRF.PermutationIndex) :
    (garbleProgram parameter scalar coins).eval (publicAnswer oracle) =
      programCircuit.garble parameter scalar (coins, oracle) := by
  unfold garbleProgram
  rw [QueryProgram.eval.eq_def]
  dsimp only
  rw [QueryProgram.eval_bind, transformKey_correct, QueryProgram.eval_bind,
    curveGarble_correct, QueryProgram.eval_map, pointGarble_correct]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem evaluateProgram_correct [FieldCertificate] [GroupCertificate]
    (table : Pipeline.Table) (input : AffineInput) (labels : GarbledCircuit.LamportSignature)
    (oracle : PublicOracle FixedKeyIndex EncPRF.PermutationIndex) :
    (evaluateProgram table input labels).eval (publicAnswer oracle) =
      programCircuit.evaluate oracle table input labels := by
  simp only [evaluateProgram, programCircuit, wireCircuit, Lamport.wireCircuit,
    GarbledCircuit.mapLabels, Garbling.garbledCircuit, Garbling.evaluate, Pipeline.evaluate]
  split <;> rename_i decoded
  · simp only [decoded, Option.bind_none]; rfl
  · simp only [decoded, Option.bind_some]
    simp only [QueryProgram.eval_bind]
    rw [QueryProgram.eval.eq_def]
    dsimp only
    rw [curveEvaluate_correct, QueryProgram.eval_bind, transformMac_correct,
      QueryProgram.eval_map, pointEvaluate_correct]
    rfl

/-! ## The transmitted table

The scheme transmits `Pipeline.PackedTable`, whose rows drop two pad bits that
no message uses. The queries are the same ones the unpacked programs make: the
packing happens after every answer is in hand, and evaluation restores the
removed bits before it reads the table, so neither program changes shape. -/

/-- The garbler publishes the transmitted form of the table it assembled. -/
def packedGarbleProgram [FieldCertificate] [GroupCertificate] (parameter : Nat)
    (scalar : NonZeroScalar) (coins : PrivateCoins) :
    Program (Pipeline.PackedTable × InputMacKey) garbleQueries :=
  (garbleProgram parameter scalar coins).map fun result =>
    (Pipeline.Table.pack result.1, result.2)

/-- The evaluator reads the transmitted table and restores it before decoding. -/
def packedEvaluateProgram [FieldCertificate] [GroupCertificate]
    (table : Pipeline.PackedTable) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature) :
    Program (Option (Option Point)) evaluateQueries :=
  evaluateProgram table.unpack input labels

set_option backward.isDefEq.respectTransparency false in
theorem packedGarbleProgram_correct [FieldCertificate] [GroupCertificate]
    (parameter : Nat) (scalar : NonZeroScalar) (coins : PrivateCoins)
    (oracle : PublicOracle FixedKeyIndex EncPRF.PermutationIndex) :
    (packedGarbleProgram parameter scalar coins).eval (publicAnswer oracle) =
      packedProgramCircuit.garble parameter scalar (coins, oracle) := by
  rw [packedGarbleProgram, QueryProgram.eval_map, garbleProgram_correct]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem packedEvaluateProgram_correct [FieldCertificate] [GroupCertificate]
    (table : Pipeline.PackedTable) (input : AffineInput)
    (labels : GarbledCircuit.LamportSignature)
    (oracle : PublicOracle FixedKeyIndex EncPRF.PermutationIndex) :
    (packedEvaluateProgram table input labels).eval (publicAnswer oracle) =
      packedProgramCircuit.evaluate oracle table input labels := by
  rw [packedEvaluateProgram, evaluateProgram_correct]
  rfl

end Kriterion.ArgoMAC.Shared
