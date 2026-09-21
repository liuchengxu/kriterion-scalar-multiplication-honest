# A smaller garbled circuit for fixed-scalar BN254 multiplication

**Result, revision 16 — all three scored metrics improve on the baseline.**
`ciphertextBytes = 8,887,896` against the baseline's 9,806,076 — a reduction of 918,180 bytes
(9.363 %). `garbleQueries = 1,394,207` against 1,759,967 and `evaluateQueries = 836,423` against
1,055,879 — both reduced by 19.92 %, at zero byte cost. Against the pre-revision baseline of 9,699,931 the
reduction is 812,035 bytes (8.372 %); the baseline grew by 106,145 bytes when the organizers replaced
a 4-way GLV search with a fixed initial state and paid for it with one extra row. The scored quantity
is the length of the encoding of the circuit's declared public value, so every byte below is a byte of
the published garbled circuit.

This is an **honest** construction: the evaluator never obtains the scalar. It receives 91
offset-blinded points and Horner-sums them into `s·P`; each row is 7-way ambiguous in its digit,
and recovering `s` from `s·P` is a discrete log. No simulator shortcut is used — the privacy proof
is the baseline's, carried across the change by an explicit adapter.

---

## 1. What the circuit is, and where the bytes go

The garbler holds a nonzero scalar `s`; the evaluator supplies affine coordinates. Per row `i` the
evaluator reconstructs `ρᵢ·(Oᵢ + φ^{dᵢ}(P))` from masked coefficients, and a cleartext Horner sum
cancels the offsets (`clampedFirst` forces `Σ radixⁱ·Oᵢ = 0`) to give `s·P`. The scalar is written
in radix `2 − ω` (Eisenstein norm 7), which needs **91 digits** for 254 bits.

Each row publishes, per coordinate, a handful of masked coefficients, and each coefficient's mask is
supplied by a **digit adaptor**: 254 ciphertexts, one per input bit, 32 bytes each.

```
one adaptor            = 254 × 254 bits, packed          = 8,065 B
one row (X + Y + Z)     = 12 adaptors + 14 coefficients    = 97,225 B
curve gadget                                               = 40,421 B
91 rows + curve gadget                                   = 8,887,896 B
```

**99.6 % of the circuit is per-bit ciphertexts.** The input MAC is already computed once and shared
across all 91 rows; the redundancy is not there. It is in the *masks*, which must be fresh per
(row, coefficient). So the only way to shrink this circuit is to publish fewer masked coefficients,
or to make each adaptor's delivery cheaper.

## 2. Lever one: the Y row on the x-only basis (4 → 3 adaptors)

Write `n` for the masked coefficients a coordinate publishes and `J` for its adaptors. Hiding
requires

> **`n ≤ J + (values the evaluator legitimately learns)`**

because a mask must cancel the adaptor contributions **as a polynomial identity in the input** — the
table is published before the adversary chooses the input — so masks are forced affine in the
adaptors' slope and hash offsets; with `n > J + 1`, `n − J − 1` combinations of the published
coefficients are determined by the row secret alone, a checkable predicate over the 7 candidate
digits. The baseline's X row sits exactly on the boundary (`5 = 4 + 1`) and is optimal.

The Y row had one adaptor of slack: `y10` existed only to cancel a hash spill. Precisely — the
quadratic coefficient is masked as `(c₅ + r₅)y²`, the `y8` adaptor contributes `(−r₅y + r₈)y`, so their
sum leaves an unwanted **linear** term `r₈y`; and the Y table publishes no linear-`y` coefficient
(`c₂ := none`) to absorb it. `y10` contributes `−r₈y + r₁₀`, and the published constant subtracts
`r₁₀`. On curve, `y² = x³ + 3`, so

```
c₀ + c₁x + c₄x² + c₅y²  =  (c₀ + 3c₅) + c₁x + c₄x² + c₅x³
```

and the x-only cubic basis lets **every** spill be absorbed into the existing three-adaptor chain and
the published constant, so no *extra canceller-only* adaptor is needed. Note that cancellation still
happens throughout the chain — what disappears is the spill into a monomial slot the row does not
publish. This closure is a polynomial identity: it does **not** require division by `x`, so `x = 0`
is not an exception, and the zero digit is covered by the same argument. Three adaptors, with slopes
chosen so the chain telescopes:

```
A_a (over x, ×x²) : σ_a x³ + K_a x²      σ_a := −r₅
A_b (over x, ×x ) : σ_b x² + K_b x       σ_b := −(r₄ + K_a)
A_c (over x, ×1 ) : σ_c x  + K_c         σ_c := −(r₁ + K_b)
p₃ = k₃ + r₅   p₂ = k₂ + r₄   p₁ = k₁ + r₁   p₀ = (k₀ + 3k₅) − K_c
```

Dimensions are tight: `3 + 3·254 = 765 = (4 + 3·254) − 1`, the same shape as the X template. The
basis is well-defined **because `φ⁶ = 1`** for every digit's endomorphism (`(φ³)² = (φ⁴)³ = 1`),
which the zero digit does not violate — it maps to `none` and never reaches the basis. This is the
only row with slack; the X row is already minimal, and Z stays at 5.

**This is the optimum of the whole addition-law space, not just of RCB.** An exhaustive search over
every bidegree-(2,2) complete addition law (every `μ ∈ P²` at two primes, every `GL₃` output
mixing, every slot, plus BN254 spot-verification) shows the `y²` slot is unkillable in every row of
every representative; the only generic kill is `{y, xy}`, which is exactly this x-only row; and the
minimum is `4 + 3 + 5 = 12`. The mask-dimension law is necessary but not sufficient — the geometry
forces one canceller in every triple. So `5 + 91×12 = 1,097` adaptors is the floor of this design.

## 3. Lever two: a 254-bit payload, without touching the proof (9,625,087 on the baseline; −69,111 B on top of lever one)

`Ciphertext := BitVec 256` and `encrypt label message := padBytes label ^^^ fieldBytes message`,
where the pad is a **full 256 bits**. Since `message < p < 2^254`, the top two bits of every
ciphertext are pure pad and carry no message.

Dropping them is not free, and this is the subtle part. Two statements go **false** — not ill-typed
— if the published table is shrunk:

- `bitAdaptorGarble_eq_iff` identifies the garbler's table *plus hash lift* with exactly five
  permutation constraints; with a 254-bit row the pad fiber is 4-to-1 and the forward direction
  fails. Its consumer appears in 20 files.
- `tableBlocksEquiv` feeds `fullCircuitSource_card = |Block| ^ (5 · |RawCircuitGate|)`, the
  **denominator of the real-transcript mass**. `2^254 ≠ 2^256`.

The proof counts one published row as exactly 256 bits of oracle entropy across 301,752 gates, so
there is no local repair — the *mass* propagation is the cost.

**The resolution separates two objects that were conflated: the table the proof reasons about, and
the value that goes on the wire.** `Ciphertext`, `padBytes`, `fieldBytes`, `encrypt` and `Table`
stay at 256 bits, so all the oracle bookkeeping is untouched. The wire gets a 254-bit `Payload`; a
mirror packed public type is connected by `GarbledCircuit.mapPublic scheme pack unpack`, and the
obligations transfer through `mapPublic` — **privacy is not re-proved at all**, because both
experiments are pushed forward by the same map, preserving work and advantage. The entire cost of
the construction change on the existing proof is **one declaration** (`padGate_evaluate_of_matches`).

Each adaptor packs to `254 × 254 bits = 64,516 bits → 8,065 B` against 8,128 B = **−63 B**, times
1,097 adaptors = **−69,111 B**.

Each adaptor packs to `254 × 254 bits → 8,065 B` against 8,128 B: 63 B saved and 4 bits wasted,
because `Encoding` composes byte-aligned components. The masked coefficients are packed per
row-coordinate rather than individually.

## 4. What is deliberately left on the table

- **548 B** of per-adaptor rounding (4 spare bits × 1,097 adaptors). Joint packing across adaptors
  would recover it, at the cost of a much less legible encoder.

**Taken:** the **3,003 B of `Option` tags** (11 per row-coordinate × 3 × 91). Row identity is
statically known and the present/absent pattern is fixed per row, so the transmitted tables now carry
only the used slots and no tags at all — 637 B of which was paid for absent fields *no evaluator ever
reads*. That change went through the same `mapPublic` boundary, so the proof's own table type and
every privacy statement are untouched.

548 B is 0.006 % of the circuit and is the last priceable item in this design.

## 5. Honest disclosure

- **The scalar is not disclosed.** The evaluator obtains `s·P`; recovering `s` needs a discrete log.
  The 91 rows are information-theoretically 7-way ambiguous in their digits.
- **No simulator shortcut.** The simulator is the baseline's; `mapPublic` transfers it rather than
  replacing it. There is no `Classical.choose`-based discrete log and no conditional disclosure.
- **The metric is the encoding's, and the encoding is the construction's choice** — that is the
  challenge's rule (`ciphertextSize` requires only that the declared count *equal* the encoding
  length). The packing above is ordinary bit-packing of a value the evaluator can decode exactly,
  not a relocation of payload into the Lamport labels, which the challenge forbids and which this
  construction does not do: the labels remain exactly the 508 selected blocks.

- **The revision-16 obligation is met, including its query bounds.** Revision 15 replaced the
  existential simulator — `∃ simulator, …` — with a requirement that the privacy proof supply a
  finite `Cryptography.BoundedMachine.Machine` for the complete simulator, with the simulator paying
  machine costs. The packed scheme's obligations are discharged by `Shared.packedCircuit`
  (`Shared.wireCircuit.mapPublic Table.pack PackedTable.unpack`) together with `packedCompatible`,
  `packedPerfectCorrectness` and `packedCiphertextSize`, which **carry the baseline's proofs across
  the packing rather than replacing them**; `adaptivePrivacy` is still
  `ArithmeticSimulator.compiledAdaptivePrivacy`. The packed boundary is a *type-level* relabelling of
  the transmitted value, so the bounded machine is the baseline's, unchanged.
- **One raised kernel budget, disclosed.** `Submission.lean` sets `set_option maxHeartbeats 4000000`
  for a single check. The expense is an **additive type-level comparison** around `scheme`/`encoding`
  — `Solution`'s later field types apply `encoding` to what `scheme` returns — measured at
  **489 s** at that budget against a timeout at the default of 200,000. It is **not** a proof
  problem: with all nine proof fields replaced by `sorry` the kernel still exceeds 100,000
  heartbeats, and replacing `scheme` as well drops the check to 2 s. `attribute [local irreducible]
  Wire.encoding` is already in force here and in `Proof/SharedGarbling.lean`; it binds the
  *elaborator*, not the kernel, so it does not reach this. No proof depends on the budget, and the
  previously accepted revision shipped the same line for the same check.

## 6. Verification

Checked locally with the platform's own `verifier.mjs` — the same five gates it runs:

```json
{"checks": {"layout":"pass","build":"pass","obligation":"pass",
            "axioms":{"result":"pass","list":["propext","Classical.choice","Quot.sound"]},
            "lint":"pass"},
 "metrics": {"ciphertext_bytes": 8887896},
 "diagnostic": null}
```

It is repeatable — the same JSON twice, in **18m44.6s** each time, against the platform's 55-minute
limit (and less than the ~23 min the previously accepted run took there). The build inside the run is
`lake build Kriterion Construction Proof Submission` under the verifier's own generated lakefile, from
scratch: 4,497/4,497 jobs including `Proof`.

`#print axioms Submission.solution` → `{propext, Classical.choice, Quot.sound}`. No `sorry`, no
`axiom`, no `native_decide`, no `implemented_by`, no `extern`. The single `noncomputable` is
`Simulator.mapPublic`, mirroring the baseline's own `noncomputable Simulator.mapLabels`, and it lives
under `Proof/`, not `Construction/`.

Every step was reviewed by an independent lane that was told to distrust the reports it was handed,
and several of those reviews overturned claims made during the work — including two of the author's
own designs (`B′` and option `A`), one prescribed proof lemma that was provable but unusable, and a
"leaf lemma" whose single misjudged member turned out to be the bridge into the mass accounting.

## 7. Provenance

Derived from the `argomac-lean` baseline and the revision-16 challenge library. Two levers were
developed against the pre-revision baseline (`711689cd`) and then **rebased onto the organizers'
rewritten baseline** (`Kriterion-cc/argomac-lean@6796e286`) after revision 15 changed the privacy
obligation; the third lever, the query pruning, was added after the entry was **ported to
revision 16** (`argomac-lean@c564e51f`, whose 9,806,076 bytes, 1,759,967 and 1,055,879 queries are
the current reference). Revision 16 scores a bounded query program for the garbler and the
evaluator, and the entry's programs enumerate only the twelve adaptor kinds each row reads — X
omits `x7`, and the Y row dropped `y8` and `y10` — where the baseline enumerates all fifteen. The
rebase restored the whole machine
layer and, along the way, corrected 33 statements in that tree that were false under the new
construction — including two that were provably false rather than stale. The full cost
model — the mask-dimension law, the spill-routing rule, the eleven closed doors, and the
addition-law search that fixes the floor at 12 adaptors per row — is documented alongside the
implementation; the design space is written down there rather than here so that this file stays a
description of the artifact.
