import Proof.Privacy.Simulator.Arithmetic.EncLinkObserve

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle

/-- The source masks one accepted finite oracle reply with the key and selected label. -/
def encLinkMaskReply (secondKey label : Block) (result : Fin (2 ^ 128) × SparseOracleFamily) :
    Block × SparseOracleFamily :=
  ((Security.SimulatorMachine.blockFin.symm result.1 ^^^ secondKey) ^^^ label, result.2)

/-- The source row has the exact joint operational law for its stored output label and all oracles. -/
theorem encLinkRowSamples_source [BN254.FieldCertificate]
    (attempts : Nat) (state : SparseOracleFamily) (memory : Memory)
    (index : EncPRF.PermutationIndex) (indices : List EncPRF.PermutationIndex) (suffix : List Bool)
    (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (secondKey label : Block) (key : memory.ram 40 = secondKey.setWidth 256)
    (selected : memory.ram (memory.ram 32) = label.setWidth 256) :
    (encLinkRowSamples attempts state memory index (indices.flatMap encLinkIndexBits ++ suffix)
      (encLinkInput memory firstKey)).map (encLinkRowValue output) =
      (drawCutoffLaw attempts ((state.permutations (encLinkPhysicalIndex index)).forward
        (encLinkInput memory firstKey))).map (Option.map fun result =>
          encLinkMaskReply secondKey label
            (result.1, state.updatePermutation (encLinkPhysicalIndex index) result.2)) := by
  let rest := indices.flatMap encLinkIndexBits ++ suffix
  let prepared := encLinkPrepared memory index rest
  let oracle := encLinkPhysicalIndex index
  let input := encLinkInput memory firstKey
  let samples := internalForwardSamples attempts (state.permutations oracle).base.used
    (state.permutations oracle).overlay.length prepared
  let observed := fun result : Memory × Nat => (queryValue result.1).map fun word =>
    let value := sparseWordValue (2 ^ 128) (by decide) word
    (value, state.updatePermutation oracle (programmedForwardNext (state.permutations oracle) input value))
  have mapped : (encLinkRowSamples attempts state memory index rest input).map (encLinkRowValue output) =
      (samples.map observed).map (Option.map (encLinkMaskReply secondKey label)) := by
    rw [encLinkRowSamples, PMF.map_comp, PMF.map_comp]
    change samples.bind _ = samples.bind _
    apply Security.ThreePhase.bind_eq_on_support
    intro result supported
    have same := encLinkRow_observe attempts state memory result.1 result.2 index indices suffix firstKey
      output limit ready supported secondKey label key selected
    simpa only [observed, encLinkMaskReply, Function.comp_def, Option.map_map] using congrArg PMF.pure same
  rw [mapped]
  have room := encLinkInvariant_room state memory index indices suffix firstKey output limit ready
  have fit : 2 * ((state.permutations oracle).base.used + 1) ≤ 2 ^ 110 := by dsimp only [oracle]; omega
  have law := internalForwardSamples_family_joint attempts prepared state oracle input
    (encLinkPrepared_family memory index rest state ready.represented ready.capacity)
    (encLinkPrepared_values memory index rest).2.1
    (encLinkInput_operand state memory index indices suffix firstKey output limit ready)
    fit (ready.capacity.overlay oracle)
  change samples.map observed = _ at law
  rw [law, PMF.map_comp]
  simp only [Function.comp_def, Option.map_map]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
