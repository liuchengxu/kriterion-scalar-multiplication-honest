# Proofs

This review checks the game interface, sampling laws, proof reuse, and compiler cost.
The review uses the upstream challenge at commit `420b229ceaafed446bffd5504d877cbc92a6b6e4`.
The challenge pins its library to commit `9db89922df1a86350f2617c7734fdd9e9219d212`.
All 14 formal Lean files match between these revisions.

The [upstream statement](https://github.com/babylonlabs-io/kriterion/blob/420b229ceaafed446bffd5504d877cbc92a6b6e4/examples/bn254-scalar-multiplication/challenge.yaml) defines the requirements.
The [pinned obligation](https://github.com/SebastianElvis/kriterion/blob/9db89922df1a86350f2617c7734fdd9e9219d212/examples/bn254-scalar-multiplication/formal/Solution.lean) defines the checked interface.

## Proof tree

`Proof.lean` exports four property roots to `Submission.solution`.
This tree shows their main supporting results.
The tree omits intermediate lemmas.

```text
Proof.lean
+-- Correctness.lean
|   +-- functionCorrect
|   `-- perfectCorrectness
|       +-- Correctness/RCBComplete.lean
|       |   +-- evaluateCorrectValid
|       |   `-- evaluateCorrectInvalid
|       `-- Correctness/Base7Termination.lean
|           `-- shortInitialTerminates91
+-- Privacy.lean
|   +-- topologyConstant
|   `-- adaptivePrivacy
|       `-- concreteAdaptivePrivacy
|           +-- concreteSmallSourceRatio
|           |   +-- Source/Valid/ValidEndpointRatio.lean
|           |   |   `-- validGhostEndpoint_mass_ge
|           |   `-- Source/Invalid/InvalidGhostEndpoint.lean
|           |       `-- invalidGhostEndpoint_mass_ge
|           `-- concreteAdaptivePrivacy_of_smallSourceRatios
|               +-- fullGateGhostRatio_event_bound
|               `-- Bounds/AdaptiveLossAccounting.lean
+-- LamportCompatibility.lean
|   `-- Lamport.compatible
|       `-- Lamport.encodeSelectsLabels
|           `-- LamportCompatibility/Labels.lean
|               `-- selectedLabels_eq
`-- CiphertextSize.lean
    `-- Wire.ciphertextSize
        `-- Construction/ArgoMAC/Encoding.lean
            `-- garble_length
```

The `Source/` and `Bounds/` paths in the privacy branch start inside `Proof/Privacy/`.
The `Construction/` path starts at the repository root.
Shared lemmas make the actual dependencies a directed acyclic graph.
`Proof/Shared/` supplies common arithmetic and probability results.
`Proof/Privacy/Distribution/`, `Programming/`, `Collision/`, and `Transcript/` support the privacy bounds.
`Proof/Privacy/Simulator/` connects sparse execution and finite sampling to the ideal game.
The sampling section below lists these simulator laws.

## Game interface

| Requirement | Review result |
| --- | --- |
| Correctness | `Proof.Correctness` proves the upstream function and perfect correctness fields. Invalid inputs produce `some none` because the scheme output type is `Option Point`. |
| Public topology | `Security.topologyConstant` proves that the topology does not depend on the scalar. |
| Adaptive input | The upstream `realGame` gives the public table to `chooseInput` before label selection. `Security.adaptivePrivacy` uses this game directly. |
| Randomness | The game samples the complete finite tape uniformly. `Seed.randomness 0` supplies a nonempty witness. The game does not fix the tape to that witness. |
| Public queries | The handlers expose fixed permutation, EncPRF, and hash queries. The permutation interfaces include forward and inverse queries. The transcript interpreter preserves private samples and records public answers. |
| Simulator information | The first stage receives only topology. The second stage receives retained state, selected input, and output. Both stages use private coins. |
| Work and advantage | The root uses upstream `ConcreteAdaptivePrivacy` with 100 bits. Upstream counts both query budgets plus one decision step. The root accepts no caller-supplied game or reduction. |
| Lamport labels | `Lamport.compatible` proves selection of 508 labels. The lower 254 bits represent `x`. The next 254 bits represent `y`. Upstream `LamportCompatibility.encodeVerifies` then proves the matching hash-lock equations. |
| Public encoding | `Wire.ciphertextSize` proves 9,699,931 bytes for every scalar and tape. `Wire.encoding` preserves the complete public table. |

The three-phase extension proves equality with the corresponding two-phase game distributions.
The extension retains the same work count plus its additional query budget.
The main obligation remains the upstream two-stage game.
The result covers fixed BN254, ideal oracles, and one selected encoding.
The result does not establish concrete AES or SHA256 security.
This interface review does not constitute an independent audit of every supporting proof.

## Sampling laws

The sparse permutation stores a partial bijection.
A fresh forward query selects a uniform unused output.
A repeated query returns the stored answer.
An inverse query uses the same state.
Fresh programming preserves earlier pairs.
A conflicting program retains the earlier answer and records the bad event.

| Law | Source |
| --- | --- |
| Forward and inverse joint distributions | `SparsePermutation.forward_joint` and `SparsePermutation.inverse_joint` in [OperationalOracleLaw.lean](Privacy/Simulator/OperationalOracleLaw.lean) |
| Adaptive query sequences | `adaptive_joint_law` in the same file |
| Simulator state and programming | `combined_adaptive_joint` in [SimulatorMachineLaw.lean](Privacy/Simulator/SimulatorMachineLaw.lean) |
| Original ideal game | `operationalIdealGame_eq` in [SimulatorPrivacy.lean](Privacy/Simulator/SimulatorPrivacy.lean) |
| Finite implementation | `game_error` and `privacy` in [SimulatorTotalImplementation.lean](Privacy/Simulator/SimulatorTotalImplementation.lean) |

Lazy sampling preserves the exact permutation law when each fresh query uses unused outputs.
A random function permits output collisions.
A permutation does not permit those collisions.
The total finite implementation uses at most 256 attempts per integer draw.
Its error from the exact ideal game is at most `(1813496 + q) / 2^256`.
Its privacy theorem includes this error and retains the 100-bit bound.
The exact law and the finite implementation therefore have separate theorems.

## Proof changes

- The valid and invalid endpoint bounds now use `theorem` with explicit conclusions.
- Their proofs use `Subsingleton.elim` to remove duplicate instance conversions.
- The oracle proof uses VCV-io's `PMF.uniformOfFintype_map_of_bijective` directly.
- The distribution proofs share one `uniform_product_bind` lemma.
- The source-ratio and correlated programming lemmas remain local because they depend on ArgoMAC state.
- The changes use the existing dependency pins.

Each future proof task should state its target theorem, hypotheses, and required check.
A direct inequality proof should retain its direct form.
A contradiction proof should expose the conflicting pair or bound.
A reduction should name the upstream game that its conclusion uses.

## Compiler cost

The measurements use Lean 4.33.1 on the local Mac.
Each command checks one source module after its imports build.
The RSS column reports the maximum resident set size from `/usr/bin/time -l`.
The command includes Lake startup and Lean imports.

| Module | Elapsed seconds | User CPU seconds | System CPU seconds | Maximum RSS |
| --- | ---: | ---: | ---: | ---: |
| `PublicDistribution` | 56.36 | 55.52 | 3.74 | 9.50 GiB |
| `ActualMaskSource` | 34.29 | 32.34 | 2.08 | 6.32 GiB |
| `SimulatorTotalImplementation` | 3.24 | 2.12 | 1.78 | 3.05 GiB |

The kernel checks each `biquadraticGarbleX_coefficients`, `biquadraticGarbleY_coefficients`, and `biquadraticGarbleZ_coefficients` proof in about 17 seconds.
The kernel checks each of the four `actual*MaskSample_table` proofs in about 8 seconds.
These declarations account for most of the measured module time.
The simulator measurement checks only its final module with its dependencies already built.
System load can affect these local measurements.
Nested and asynchronous profiler entries overlap.
Their durations must not form an additive total.
These compiler measurements do not measure earlier agent searches or simulator design time.
The available build logs cannot separate those historical activities.
The measurements do not establish a compiler speed improvement from this refactor.

You can repeat a measurement from the upstream challenge directory:

```sh
/usr/bin/time -l lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 argomac-lean/Proof/Privacy/Distribution/PublicDistribution.lean
```

## Fixed permutation slots

[QueryCounts.lean](Privacy/Transcript/QueryCounts.lean) proves `pipelineGateSchedule_query_counts`.
The theorem applies to the complete gate schedule.

| Quantity | Count |
| --- | ---: |
| Gates | 301,752 |
| All five slots per gate | 1,508,760 |
| Selected slots across the complete schedule | 603,504 to 905,256 |

Each gate has three hash slots and two pad slots.
Each selected branch uses three hash slots or two pad slots.
These counts exclude EncPRF calls and hash-oracle calls.
An invalid evaluation can stop before it reaches every gate.
These counts do not replace the upstream adversary work function or the byte metric.
They do not measure Rust execution time.

## Upstream verification

The upstream `verifier.mjs` checks a clean copy of the final submission against the pinned library.
The checked Lean files match the workspace Lean files exactly.

| Check | Result |
| --- | --- |
| Allowed file layout | Pass |
| Lean build | Pass |
| `Submission.solution : Kriterion.Solution` | Pass |
| Axiom audit | Pass: `propext`, `Classical.choice`, `Quot.sound` |
| Computability and source lint | Pass |
| `Kriterion.Benchmark.ciphertextBytes` | 9,699,931 bytes |

The full challenge build also passes with 3,666 jobs.
The separate `lake env lean argomac-lean/tests/Operational.lean` check passes.
All 223 proof modules remain reachable from the four roots.
The proof import graph has no cycles.
This refactor removes 24 Lean lines overall.
