# Proof map

The local challenge checks `Submission.solution : Kriterion.Solution`.
The Lake configuration pins the external challenge library.
The construction uses 92 digits and three shared permutation slots.
The canonical ciphertext contains 9,806,076 bytes.

## Construction properties

| Property | Main source |
| --- | --- |
| Complete scalar multiplication | `SharedGarbling.lean` and `Correctness/RCBComplete.lean` |
| Base-7 termination | `Correctness/Base7Termination.lean` |
| Three shared permutation slots | `SharedOracle.lean` |
| Selected Lamport labels | `LamportCompatibility.lean` |
| Canonical ciphertext size | `SharedGarbling.lean` and `CiphertextSize.lean` |
| Paper block formula and tweaks | `Privacy/PaperConstruction.lean` |

The correctness proof covers every input and every random tape.
The proof includes equal points, identity results, and invalid affine inputs.
The encoding returns exactly 508 selected 128-bit labels.
The lower 254 labels encode the input x-coordinate.
The upper 254 labels encode the input y-coordinate.

The paper's coordinate formulas fail on some required inputs.
The construction uses complete homogeneous addition formulas with 13 point-adaptor families.
The [paper corrections](https://github.com/Kriterion-cc/kriterion-challenge/blob/3322a36abd962aa5960e65d7f2d8b9f72478d1e3/bn254-scalar-multiplication/PAPER_CORRECTIONS.md) record the required changes.
The challenge's `tests/PaperFormulaChecks.lean` checks the counterexamples.

## Adaptive privacy

The challenge requires one combined `AdaptivePrivacy` property.
The property bounds the real-to-ideal advantage plus the ideal-to-machine advantage.
The total allowance is `(Q + 1) / 2^100`.
The two declared adversary query budgets sum to `Q`.

The final arithmetic proof has these layers:

| Layer | Source in `Privacy/Simulator/Arithmetic/` |
| --- | --- |
| Finite source and sampling error | `SharedFiniteSourceDecision.lean` |
| Concrete setup and public bytes | `CompiledSetupProtocol.lean` |
| Adaptive input selection and public queries | `CompiledChosenProtocol.lean` |
| Online source and machine distributions | `OnlineValidConcrete.lean` and `CompiledNullProtocol.lean` |
| Output labels and retained memory | `OnlineValidJointMemory.lean` and `OnlineNullJointMemory.lean` |
| Adaptive decision and public queries | `CompiledDecisionProtocol.lean` |
| Complete game composition | `CompiledAdaptiveGame.lean` |
| Combined privacy bound | `CompiledAdaptivePrivacy.lean` |

`CompiledOnlineCouplingLaw` states the online connection.
Its two distribution equalities retain the actual machine state and the source state.
Its final state condition pays for the later public queries.
`CompiledOnlineCoupling.lean` proves this connection for both online branches.
`compiledAdaptivePrivacy` then proves the complete combined property.

The shared source uses one transcript for each shared slot.
Its forward and inverse queries use the same partial bijection.
A repeated query returns the stored answer.
A fresh permutation query samples an unused output.
A random-function query permits output collisions.
The proofs account for conflicting domain and range assignments.

The simulator receives the public topology during setup.
The online request supplies only the selected input and output.
The simulator never receives the hidden scalar.
The proof covers an adaptive input after public-circuit disclosure.

## Arithmetic machine and cost

The simulator uses fixed arithmetic instructions.
The instruction set has no Lean callbacks or arbitrary distribution values.
The machine pays for its program table and every executed instruction.
The instruction count includes random bits and data access.
The complete machine uses one cumulative counter.

`CompiledPhaseCost.lean` bounds every phase.
`CompiledBudget.lean` proves that the actual instruction count fits:

```text
B(q) = 64*q^2 + 2^27*q + 2^46
```

The variable `q` counts the adversary's queries at the current phase.
The bounded sampler uses at most 256 attempts per draw.
The sampling error contributes to the combined privacy allowance.
These bounds specify abstract machine instructions.
They do not specify processor time.

## Acceptance tests

The challenge's `lake test` command checks the complete local starter.
The test builds the public library and its regression proofs.
The test then builds `Construction`, `Proof`, `Submission`, and `BaselineTests`.
The test checks both the exported proof axioms and the final submission axioms.

The axiom checks permit only `propext`, `Classical.choice`, and `Quot.sound`.
The acceptance tests reject an incomplete adaptive privacy proof.
`Submission.solution` contains no open proof goals.
The complete `lake test` command passes.

The repository retains the older independent-role proofs for source provenance and proof reuse.
Those proofs do not replace the shared-slot construction or the bounded machine obligation.
