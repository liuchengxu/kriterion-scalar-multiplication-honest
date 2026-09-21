# Where the 9 % comes from

This document explains the theory behind the size reduction and **reconciles every byte under an explicit order of
source-level transformations**, so that each number can be checked rather than taken on trust. The order matters: a
deletion and a re-encoding interact, and §3 states which order the published attribution uses. `README.md`
describes the artifact; this file is the accounting behind it.

Two provenance caveats up front. The revision-15 baseline tree inspected here carries no Git metadata, so its
identity as `argomac-lean@6796e286` is checked against the challenge's own record rather than re-derived. And the
"exhaustive search" referred to in §5 is described in the neighbouring design notes, not reproved here.

---

## 1. The cost identity

The garbler holds a secret scalar. What it publishes is a table of rows, each computing a polynomial in the
input coordinates `(x, y)`. Every published coefficient is **masked** — a random-looking value is added so the
real coefficient cannot be read — and the masks are delivered by **digit adaptors**, each of which publishes
**254 ciphertexts**: one per bit of the input, 32 bytes each.

```
one digit adaptor   = 254 × 32 B          = 8,128 B     (one per input bit)
```

**The submitted X/Y/Z rows contain respectively 5/4/5 coefficients and 4/3/5 digit adaptors.** Adaptor counts are
not coefficient counts: the X coordinate publishes 5 coefficients on 4 adaptors, because one coefficient's mask
is absorbed into the published constant rather than given its own adaptor. The exact byte cost follows from those
counts and the encoding in §2 — this document always counts **adaptors**, never coefficients, and does not treat
the two as interchangeable.

**Adaptor blobs are 8,847,305 of the 8,887,896 encoded bytes — 99.54 %.** The input MAC is already computed once
and shared across all 91 rows; the redundancy is not there. It is in the *masks*, which must be fresh per
(row, coefficient). So the only way to shrink this circuit is to publish fewer masked coefficients, or to make
each adaptor's delivery cheaper.

As an illustration of the dominant term, before any of the levers and at the unpacked ciphertext size:

```
91 rows × 12 adaptors × 8,128 B   ≈  8.9 MB      (adaptor mass only; excludes the curve
                                                  gadget and the coefficients, and uses the
                                                  unpacked intermediate representation)
```

---

## 2. The levers

### Lever A — the Y row's canceller adaptor: **−739,648 B**

A mask's hash spill must be absorbed by something the row already publishes. If a spill would land where the row
publishes nothing, a second adaptor is needed whose only job is to cancel it.

The Y row before this work published `{1, x, x², y²}` and used **four** adaptors:

```lean
-- rebase/entry/Construction/ArgoMAC/Biquadratic.lean:104-106   (the revision-15 baseline)
let y8  := DigitAdaptor.garble oracles.y8  (-randomness.r5) inputKey.y
                                                                  -- :105 defines r8
let y10 := DigitAdaptor.garble oracles.y10 (-r8)            inputKey.y
```

`y10` is that second adaptor, and the mechanism is exact: the quadratic coefficient is masked as
`(c₅ + r₅)y²`, the `y8` adaptor contributes `(−r₅y + r₈)y`, and their sum therefore leaves an unwanted
**linear `r₈y`** term. The Y table publishes no linear-`y` coefficient (`c2 := none`), so there is nothing to
absorb it. `y10` supplies `−r₈y + r₁₀`, and the published constant subtracts `r₁₀`.

Note that the slope `−r₈` is specific to `garbleY`. The same file has two other `y10` occurrences — at `:85` in
`garbleX` and `:131` in `garbleZ` — and both use `−(randomness.r2 + r8)` instead. Only `:106` is the Y row's.

**The change.** On the curve `y² = x³ + 3`, so `c₅y² = c₅x³ + 3c₅`. The row is rewritten in the x-only cubic
basis `{1, x, x², x³}`:

```
c₀ + c₁x + c₄x² + c₅y²  =  (c₀ + 3c₅) + c₁x + c₄x² + c₅x³
```

All three adaptors now read `x`, with multipliers `x²`, `x` and `1`. Their hash offsets spill into **`x²`, `x`
and the constant**; each spill is cancelled by the next slope in the chain, and the last by the published
constant. No *extra canceller-only* adaptor is needed.

Two precisions:

- **Cancellation still happens.** In this construction, cancelling is what masking is; the arithmetic throughout
  the three-adaptor chain is a chain of cancellations. What disappears is specifically the spill into a monomial
  slot the row does not publish.
- **The closure is a polynomial identity**, and does not require division by `x`. So `x = 0` is not an exception,
  and the zero digit is covered by the same argument. Two separate facts are at work: the cancellation identity
  holds for **every** input, while equality to the original `y²` polynomial additionally requires the curve
  equation.

| | adaptors in the Y row |
|---|---|
| baseline | **4** — `y8` (`:104`), `y10` (`:106`), `x7` (`:108`), `x9` (`:110`) |
| ours | **3** — `y6`, `x7`, `x9`, all reading `x` |

Sources: `rebase/entry/Construction/ArgoMAC/Biquadratic.lean` against
`rebase2/entry/Construction/ArgoMAC/Biquadratic.lean`, with the rebound polynomial at
`FieldMacToECMac.lean:169-172`:

```lean
def evaluateCubicY (coefficients : Coordinates.Coefficients) (input : AffineInput) : BaseField :=
  coefficients.constant + 3 * coefficients.ySquared + coefficients.x * input.x +
    coefficients.xSquared * input.x ^ 2 + coefficients.ySquared * input.x ^ 3
```

**Arithmetic.** One adaptor removed on each of 91 rows, at the *unpacked* size — the deletion is attributed
before the packing lever, for the reason in §3:

```
91 × 8,128 = 739,648 B
```

**Structural evidence.** The adaptor-call counts inside `garbleY` (four versus three) establish the deletion.
The row's encoded length falls from 32,651 to 24,322, but that 8,329-byte delta includes encoding changes as
well as the deletion, so the length values alone do not isolate the cause. (The baseline theorem is
`Wire.y_length`; the submitted one is `Wire.yRow_length`.)

---

### Lever B — the 92nd row: **−106,145 B**

The scalar is written in a number system (radix `2 − ω`) whose expansion needs about 91 digits. The
revision-15 baseline selects **one fixed initial state** and needs **92**:

```lean
-- rebase/entry/Construction/ArgoMAC/Base7.lean:268
terminal : ∀ scalar, after 92 (glvInitial scalar) = ⟨0, 0⟩
```

The tree also contains a **four-corner selection**: `shortInitial` checks four shifted initial states and takes
one that terminates in **91** steps — and that is a **proved theorem**:

```lean
-- rebase2/entry/Proof/Correctness/Base7Termination.lean:678
theorem shortInitialTerminates91 (scalar : BN254.ScalarField) :
    after 91 (shortInitial scalar) = ⟨0, 0⟩
```

It is an unconditional, all-scalar proof: a geometric covering argument establishes that one of the four
candidates has small Eisenstein norm (for *every* round index `k`), then an induction on the norm gives
termination. It is **not** a test over sampled scalars, and the `else` branch of `shortInitial` **is justified** —
if candidates 0, 1 and 2 fail, existence supplies a terminating candidate, and the four-way split leaves
candidate 3 (see `Base7Termination.lean:680-693`).

**The change.**

| | value |
|---|---|
| `FieldMacToECMac.outputMacCount` | **92** → **91** |
| certificate | `after 92 (glvInitial …)` → `after 91 (shortInitial …)` |
| `Construction.digits` | `decompose 92 (glvInitial …)` → `decompose 91 (shortInitial …)` |

**Arithmetic.** One row at the *baseline* row size, because a row is removed before its successor rows are
re-encoded:

```
106,145 B  = one baseline row
```

**What this is *not*.** The 92nd row is **not** a zero or dummy row. It can carry a real, nonzero digit, so the
saving comes from a different initial-state *algorithm*, not from deleting padding. (An earlier telling of this
document said otherwise; it was wrong.) The specific claim that some baseline scalar's 92nd digit is
`negOmegaSquared` is an **exact-integer computation against the baseline's own definitions, not a
kernel-checked witness** — it should be treated as an illustration rather than a verified example.

**Stronger? No — smaller.** Both certificates are abstract hypotheses at their generic use sites, and **both have
proved instances**: the baseline discharges `glvInitialTerminates92` from a real norm-bound proof
(`rebase/entry/Proof/Correctness/Base7Termination.lean:708-733`, instantiated at `:735-737`), and we discharge
the submitted certificate from `shortInitialTerminates91` at the same place in our tree. We are not stronger
because the baseline lacked a proof; we use fewer rows with a different selection.

---

### Lever C — the payload is 254 bits, not 256: **−69,111 B**

A ciphertext is `padBytes ⊕ fieldBytes message`, where `padBytes` is a full 256 bits. The BN254 base field
modulus lies strictly between `2^253` and `2^254` (`formal/BN254.lean:17-18`), so `fieldBytes` zeroes the top
two bits of every message:

```
Ciphertext = padBytes(256 bits) ⊕ message(< 2^254)     → the top 2 bits are pure pad
```

Dropping them is **lossless** in the sense that matters — the message and the evaluation are preserved, though
the original 256-bit ciphertext is not recovered (unpacking restores the removed bits as zeros). The mask is
projected too: `decrypt` XORs the projected pad, not a truncated ciphertext against a full-width pad
(`BitAdaptor.lean:64-75`). The proof uses `message.val_lt` and the modulus bound, and `Packed.lean`'s
`evaluate_unpack_pack` proves evaluation is unchanged by the round trip.

**Arithmetic.** One adaptor's payload is `254 × 254 = 64,516` bits. Byte-aligned, that is
`ceil(64,516 / 8) = 8,065` bytes — **64,520 stored bits, i.e. four alignment bits per adaptor** — against
8,128 bytes, so **63 bytes** are saved on every adaptor, over the whole circuit:

```
(5 + 91 × 12) × 63 = 1,097 × 63          =  −69,111 B
```

The source documents the alignment explicitly (`Encoding.lean:59-63`, `Simulator/PublicWire.lean:18-23`).

---

### Lever D — tags and coefficient packing: **−3,276 B**

Two smaller savings in the same encoding change:

| | bytes |
|---|---|
| **presence tags** — the row shape is statically fixed, so `Option` presence carries nothing — 11 tags × 3 row-coordinates × 91 rows | **−3,003** |
| **coefficient packing** — 5/4/5 coefficients at 32 B each become 159/127/159 B (254 bits each), so 1 byte per group × 3 groups × 91 rows | **−273** |

```
5 × 254 = 1,270 bits → 159 bytes, against 160
4 × 254 = 1,016 bits → 127 bytes, against 128
3 × 254 =   762 bits →  96 bytes, against  96   (the curve gadget saves nothing here)
```

The curve gadget also carries no tags.

---

## 3. The telescoping

```
  9,806,076   revision-15 baseline
−   106,145   Lever B — one fewer row (92 → 91)
−   739,648   Lever A — the Y canceller adaptor, at unpacked size (91 × 8,128)
−    69,111   Lever C — packing adaptor payloads to 254 bits (1,097 × 63)
−     3,003   Lever D — presence tags (91 × 3 × 11)
−       273   Lever D — coefficient packing (91 × 3)
= 8,887,896   ✓   −918,180 B, −9.363 %
```

Independently, the component changes agree:

```
curve:  315 = 5 × 63
X:      264 = 4 × 63 + 11 + 1
Y:    8,329 = 8,128 + 3 × 63 + 11 + 1
Z:      327 = 5 × 63 + 11 + 1
per retained row: 264 + 8,329 + 327 = 8,920
```

**Which baseline you compare against changes the story, and it is worth being explicit about it.**

| comparison | total | levers |
|---|---|---|
| vs the **pre-revision** baseline (9,699,931) | −812,035 B, −8.372 % | A, C, D — **Lever B contributes no additional saving here**, because that baseline already used `decompose 91 (shortInitial scalar)` |
| vs the **revision-15** baseline (9,806,076) | −918,180 B, −9.363 % | A, B, C, D |

The two baselines differ by exactly one 106,145-byte row in the size ledger. That explains the *size* difference
and does not imply their source changes consisted only of adding a row.

**The A/C split is ordering-dependent.** A **digit adaptor** deleted *before* packing saves 8,128 B; the same
adaptor deleted *after* packing would have saved 8,065 B. Taking packing first would attribute
`91 × 8,065 = 733,915` to deletion and a further `91 × 63 = 5,733` to packing — which is `739,648` in total
either way, but makes C 74,844 B rather than 69,111 B. Neither attribution is uniquely intrinsic; the order
above is stated so the published figures are reproducible.

---

## 4. The query metrics

Revision 16 scores two quantities beside the byte count: `garble_queries` and `evaluate_queries`. These are not
sizes. They are the number of oracle calls the garbling program and the evaluating program are declared to make,
and the declaration lives in the program's **type** — `Program (… ) garbleQueries` — so it is what the challenge
measures.

The program enumerates, for each of the 91 transmitted rows, each of the three coordinates, each of the five
adaptor windows at each of the 254 input positions. That is fifteen coordinate/adaptor pairs, but only **twelve**
are read: the X row omits `x7`, and the Y row — which rebinds `y ^ 2` to `x ^ 3 + 3` — dropped `y8` and `y10`.
`Construction/OraclePrograms.lean` already recorded that about the *rows*; the program had not followed.

Pruning the three unread pairs:

```
garble_queries     1,740,917  →  1,394,207     −346,710   (−19.92 %)
evaluate_queries   1,044,449  →    836,423     −208,026   (−19.92 %)
ciphertext_bytes   8,887,896  →  8,887,896     unchanged
```

The garbling saving is exactly `91 × 3 × 5 × 254 = 346,710`, and the evaluating saving is three fifths of it —
the garbling schedule asks five queries per active gate where the evaluator asks three. Both cost **zero bytes**:
the bytes are the transmitted tables, and those did not change.

Two points this section is careful about.

- **The declared numeral is a bound, not a count.** It is an upper bound the program must satisfy, so
  *under*-declaration fails to compile while *over*-declaration compiles silently. The 19.92 % is therefore
  meaningful only because the boundary is tight, which is established by counting the straight-line query
  schedule rather than inferred from the type.
- **Pruning the evaluator needs a precondition the garbling side does not.** `Biquadratic.evaluate` does consult
  the X row's `x7`, so the pruned evaluation is sound only for tables that do not carry it — the `TransmittedX`
  property, discharged for every packed table by `transmittedX_unpack`. That is a property of the transmitted
  table, not of an arbitrary logical one, and it is why the judgement is made at the packed interface.

---

## 5. What is not claimed

- **This is not a general lower bound.** The construction achieves **12 adaptors per row**. The inspected Lean
  results establish its evaluation identities and its encoded size — **not** optimality over all complete
  addition laws. (The design notes describe a search over the bidegree-(2,2) complete addition law space at two
  primes plus spot-verification over BN254; that is a description of a search, not a proof of exhaustive
  coverage, and it is not reproved here.)
- **The row's basis, not the arithmetic, is the lever.** A row's monomial basis decides how many masks it needs,
  because it decides where a mask's spill lands. That is the transferable idea; the specific x-only cubic basis
  is one instance of it.
- **Lever B replaces one initial-state selection with another.** It does not establish that 91 is minimal, only
  that 91 suffices and is proved. Whether the organizer chose 92 for a reason the source does not record is
  **not settled** — `shortInitial` also performs data-dependent candidate checks, which is a garbler-side cost.
- **Packing is a projection, not a relabelling.** The internal public table is 256-bit and packing is
  many-to-one onto the transmitted representation. Evaluation and privacy transfer through the adapter; this
  does **not** imply an unchanged simulator or wire layout — the concrete emitter is row-count dependent
  (`Simulator/PublicWire.lean:34,61-63`).
- **Both termination certificates are proved.** Where this document says the baseline "assumes" the 92-round
  property, it means the certificate is a typeclass hypothesis at its generic use site — the same structure ours
  has. It is discharged by a proof in both trees.
