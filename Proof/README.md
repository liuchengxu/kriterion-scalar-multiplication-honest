# Proof map

The local challenge checks `Submission.solution : Kriterion.Solution`.
The Lake configuration pins the external challenge library.
The construction uses 91 digits and three shared permutation slots.
The canonical ciphertext contains 8,887,896 bytes.

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
The construction uses complete homogeneous addition formulas with 12 point-adaptor families.
The [paper corrections](https://github.com/Kriterion-cc/kriterion-challenge/blob/aaf278948a4127f99ee6752c7cec4b9f9bd43615/bn254-scalar-multiplication/PAPER_CORRECTIONS.md) record the required changes.
The challenge's `tests/PaperFormulaChecks.lean` checks the counterexamples.

## Adaptive privacy

The challenge requires `OracleAdaptivePrivacy` against a closed adversary.
The real and ideal games use one fixed lazy oracle.
The real garbler receives independent private coins.
The adversary chooses its input after it receives the public circuit.

The oracle serves the adversary's queries directly.
Repeated queries return the stored answer.
Forward and inverse queries share one partial bijection.
Fresh permutation queries sample unused outputs.
Hash queries permit output collisions.

The simulator can inspect the oracle and program fresh mappings.
Permutation programs require an unused domain and range.
Hash programs require an unused input.
A refused program aborts the ideal game.
The original collision event covers this abort.

| Proof | Source |
| --- | --- |
| Construction query results and bounds | `../Construction/OraclePrograms.lean` |
| Lazy real game and complete oracle law | `SharedOracle.lean` |
| Adaptive public queries | `Privacy/Simulator/PublicOracleLaw.lean` |
| Fresh programs and aborts | `Privacy/Simulator/StrictOracleLaw.lean` |
| Strict source privacy | `Privacy/Source/StrictGateSource.lean` |
| Finite private sampling | `Privacy/Source/StrictSourceSampling.lean` |
| Public challenge bound | `Privacy/Source/StrictWirePrivacy.lean` |
| Closed machine execution | `Privacy/Simulator/Arithmetic/OnlineLazyExecution.lean` |
| Complete machine privacy | `Privacy/Simulator/Arithmetic/CompiledAdaptiveGame.lean` |

## Machine cost

The simulator uses fixed arithmetic and oracle instructions.
The instruction set has no Lean callbacks or arbitrary distributions.
The machine pays for its instruction table and both stage limits.
The total must not exceed `2^60`.
Each executed instruction consumes one unit of stage fuel.

The simulator receives public parameters during setup.
The online request supplies only the selected input and output.
The simulator never receives the hidden scalar.
Its private samplers use at most 256 attempts per draw.
The finite sampling error contributes to the privacy allowance.
These limits specify abstract instructions, not processor time.

The adversary also uses a closed instruction table.
Its total work includes its table, both stage limits, and the decision allowance.
The privacy bound uses this total work.
The BN254 axiom list is empty.

## Acceptance tests

The challenge's `lake test` command checks the local baseline.
The test builds the public library and its regression proofs.
The test then builds `Construction`, `Proof`, `Submission`, and `BaselineTests`.
The test audits every imported construction and proof declaration.
The test also audits the final `Submission.solution` declaration.
The audits permit only `propext`, `Classical.choice`, and `Quot.sound`.
