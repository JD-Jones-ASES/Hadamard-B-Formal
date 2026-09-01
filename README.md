# hadamard-b-formal

A Lean 4 / Mathlib formalization of part of the theorem layer of Hadamard-B.
Twenty-six theorems are compared, over a shared surface of fifty-eight
definitions: an exact characterisation of when a Goethals--Seidel array over a
finite abelian group extends to a Hadamard matrix through a border whose strips
are constant on the cosets of a subgroup (Theorem A, an iff); the house form of
that characterisation and its two classical degenerations (Theorem B); the two
row-sum rows D5 and D6 of Theorem C — and only those two; the character-twist
layer (Lemma T and the `ψ(ρ) = 1` conjugation); Theorem D's clauses (D-a)
through (D-e), including the degenerate-branch collapse (D-a′) with its
entry-for-entry `H = H₁` equality and its converse, and both directions of the
(D-e) transport; the seed-problem bijection of §1.6 — and only that clause; and
two kernel-checked instances taken through the theorem rather than through a
matrix product. All twenty-six theorems are kernel-checked on Lean's three
standard axioms.

The compared surface is therefore a **complete resolution of the `s = 1`,
`i = 2` border system in the sense of Theorem D's own clauses**, with two
exclusions to state in the same breath: §1.6's characteristic-subgroup and
automorphism-equivariance clauses are not formalized, and neither is the 768²
census behind (D-e), which is a Python certificate in the source repository
rather than a theorem here.

## Registry

Registered in the Palomar Registry as
[PALOMAR-2026-09-01-000006](https://palomar-registry.org/entry?id=PALOMAR-2026-09-01-000006&version=1)
(version 1, 2026-09-01), pinned to commit
`d99c0180872e4213e54272f9699d28f28032a2a3`. The registration records that
the twenty-six public theorems matched this repository's Mathlib-only
challenge surface and that their proofs replayed in Lean's kernel and in
Palomar's pinned independent NanoDa kernel at that commit (mechanical
verification completed 2026-09-01T11:38:15Z; axioms `propext`,
`Classical.choice`, `Quot.sound`; MIT declared and detected). It certifies
proof replay and statement fidelity to the recorded challenge — not
fidelity to the informal source, novelty, interest, or peer review, which
remain editorial questions. Later commits here do not alter that entry,
which stays pinned to the registered commit.

The local check set — Lean build, transitive axiom audit, exporter
determinism, assembly cross-check, and the statement-parity check
(every compared theorem's fully elaborated type byte-identical between
`Challenge` and `Solution`) — is `python -B scripts/verify.py`, and it
gates every commit here. The first submission failed Palomar's Comparator
exactly where the parity check now looks; the registered commit carries
the fix and the gate.

### Why one entry

`Challenge.lean` is about 43 KiB and 946 lines. That is inside Palomar's hard
limits of 100 KiB and 1,000 lines — comfortably on bytes, with 54 lines of
headroom — and above both auditability warning thresholds of 32 KiB and 300
lines, so two mechanical warnings are expected.
The size is a deliberate choice. The twenty-six theorems are one dependency
chain over one ansatz — the coset-bordered Goethals--Seidel array — and the
fifty-eight definitions are the shared vocabulary that chain is stated in.
Splitting the tranche across entries would not divide the definitional surface;
it would replicate most of it in each entry, so a reviewer would audit `border`,
`gsBlock`, `H1`--`H4` and the instance literals several times over instead of
once. The single comprehensive entry is the smaller audit, not the larger one.

### Submission notes (drafted)

For the submission form's optional `context` field, which is published:

> This entry compares 26 theorems over 58 definitions in one Challenge, which
> trips both auditability warnings (32 KiB, 300 lines) while staying inside the
> hard limits. The theorems are a single dependency chain over one ansatz, the
> coset-bordered Goethals--Seidel array, and the definitions are the shared
> vocabulary that chain is stated in. Splitting the tranche across entries
> would replicate most of the definitional surface in each one, so the reviewer
> would audit those definitions several times rather than once; the single
> entry is the smaller audit. Every compared theorem has a plain-language
> account in the repository README, and every compared definition states its
> intended value in its docstring. The mathematical source repository is the
> author's own and is cited at a pinned commit; the account here is
> self-contained and does not depend on the reader reaching it.

### Preflight

1. Re-run the whole local check set on the exact candidate commit:
   `python -B scripts/verify.py --source-root <Hadamard-B checkout>` — isolated
   `lake build`, transitive axiom audit, exporter `--check`, assembly
   cross-check, forbidden-token scan, and list set-equality.
2. Review the snapshot for private data, credentials, identity and authorship
   leakage, and licence consistency.
3. **The source repository must be publicly cloneable at its pinned SHA before
   submission** — executed: [Hadamard-B](https://github.com/JD-Jones-ASES/Hadamard-B)
   is public as of 2026-09-01 and the pinned commit `01a7f061…` resolves
   without authentication. The account here stands without it either way.
4. JD flips this repository public at the exact final commit. Palomar checks out
   that commit, and mechanical verification runs in a public GitHub Actions
   workflow, so the repository and the commit are public from the moment of
   submission.
5. Duplicate-commit preflight: `GET
   https://data.palomar-registry.org/registration-identities/<sha256>.json`,
   where the digest covers `lowercase_repository` + NUL + `project_path_or_empty`
   + NUL + `comparator_config_path`. Its `commits` array names every commit
   already registered under that identity.
6. Invoke Palomar's protected run against that exact public commit.
7. Read the mechanical report for what it establishes — recorded Solution
   satisfies recorded Challenge, kernel and NanoDa replay — and for nothing
   else.
8. Register the **final post-repair 40-character SHA**. Not `90e5f9c…`, and no
   other pre-repair commit.
9. Retain the `scripts/verify.py` transcript and the mechanical report with the
   submission packet.

### Form coordinates

| Field | Value |
| --- | --- |
| `repository` | `https://github.com/JD-Jones-ASES/Hadamard-B-Formal` |
| `commit` | the final post-repair 40-character SHA |
| `project_path` | blank — the Lean project is at the repository root |
| `comparator_config_path` | `comparator.json` |
| `formalization_metadata_path` | `formalization.yaml` |
| `existing_id` | blank — this is a new registration |
| `authorization_relationship` | `maintainer` |
| `authorization_evidence`, `context` | optional free text, **and both are published** |

## What Lean proves

Twenty-six compared theorems, in nine groups.

**Theorem A** (`theoremA`, `theoremA_sufficiency`) — with `κ : G →+ Ḡ` a
surjective hom all of whose fibers have size `w`, sign-valued corner `E`, border
tables `P`, `Q` and seeds `x`, the bordered array `H = [[E, P̃], [Q̃, C]]` is a
Hadamard matrix of order `N = 4(|G| + s)` **if and only if** (H1) `Q Qᵀ = I₄ ⊗ M`
for some `M : Ḡ → ℤ`, (H2) `Σ PAF(t) = −M(κ t)` off the origin, (H3)
`E Eᵀ + w · P Pᵀ = N · I`, and (H4) `E Qᵀ + P Ĉᵀ = 0` against the compressed
core. The sufficiency half is stated separately with the surjectivity
hypothesis omitted, since it follows from the constant-fiber-size hypothesis;
that is the direction the two instances consume.

**Theorem B and the two classical degenerations** (`theoremB_profile`,
`goethalsSeidel_abelian`, `borderedGS_index_one`) — for the house Gram table,
(H2) *is* the two-tier autocorrelation profile
`4n·δ₀ − 4s·[t ∈ K∖0] + 4·[t ∉ K]`. Degenerating the ansatz recovers the
Goethals--Seidel theorem over an arbitrary finite abelian group (`s = 0`) and
the Wallis--Whiteman / Spence bordered construction (`s = 1`, `i = 1`), each at
an **arbitrary** reflection shift `ρ` rather than only the group inversion.

**The row-sum rows** (`D5`, `D6`) — summing the house profile over `G` gives
`Σ_q r_q² = 8n − 4w(s+1) + 4s`, using only the size of the fiber over zero; at
index one, non-negativity of a sum of squares turns that into `n(s−1) ≤ s`.
These are two rows of Theorem C. **The forced-parameter clauses D1--D4 and the
classification corollary they support are not formalized.**

**The twist** (`lemmaT`, `twist_profile_iff`, `twist_isConjugation`,
`twist_isHadamard_iff`) — `PAF_{ψx}(t) = ψ(t)·PAF_x(t)` for a `±1`-valued
character; hence at `s = 1` a quadruple satisfies the index-one profile exactly
when its twist satisfies the index-two profile; and a twist with `ψ(ρ) = 1` is
the diagonal conjugation `H ↦ S H S`, so the twisted border is Hadamard exactly
when the original is — it manufactures no new matrix.

**Theorem D, the genuine branch** (`theoremD_tables`, `theoremD_rowTable`,
`theoremD_border`, `deltaSqSum_eq_four`) — at `(s, i) = (1, 2)` the Gram table
is forced to `M(0) = 4`, `M(1) = ±4`; in the genuine branch `M(1) = −4` the
column table pair-negates onto a `4 × 4` Hadamard matrix `U`; the row table is
then forced to pair-negate and both its reduced form `p` and the corner `E` are
Hadamard; (H4), a `4 × 8` condition, collapses to the single `4 × 4` equation
`4·E = −p·Λ(d)ᵀ·U`; and the integer Parseval identity `Σ_q δ_q² = 4` holds.

**Theorem D, the (D-e) transport, in both directions** (`theoremD_transport`,
`theoremD_transport_converse`, `theoremD_transport_iff`) — doubling an index-one
border and twisting the seeds gives a valid index-two instance under the note's
condition `d = r`; that condition is not assumed but **forced**, by cancelling
two `4 × 4` Hadamard factors over `ℤ`; and the two halves package as the note's
*exactly when*.

**Theorem D, clause (D-a′), in both directions**
(`theoremD_degenerate_collapse`, `theoremD_degenerate_converse`) — in the
degenerate branch `M(1) = +4`, where `M = 4J₂`, the border data **is** index-one
data in index-two bookkeeping: `Q` pairs up equal, `P` pairs up equal, the
assembled matrix equals the index-one assembly **entry for entry**, and
(H1)--(H4) transport termwise onto the collapsed tables over a trivial quotient.
Conversely, doubling any index-one border returns (H1)--(H4) with `M = 4J₂` and
the same assembled matrix. Together these are the note's bijection.

**The index-two collapse, seed-problem clause**
(`collapse_seedProblem_bijection`) — the character twist is an involution, a
bijection of sign-valued quadruples, and a bijection carrying the `s = 1, i = 1`
seed problem onto the `s = 1, i = 2` seed problem. It is a bijection of *seed
problems*, not of matrices. **§1.6's characteristic-subgroup and
automorphism-equivariance clauses are not formalized.**

**The two instances** (`hadamard_52_bordered`, `gate52_columnTable`,
`hadamardExists_52`, `hadamard_20_bordered`, `hadamardExists_20`) — the `H(52)`
Theorem-D gate on the non-cyclic group `ℤ₂×ℤ₂×ℤ₃` in the `ε = +1` branch, whose
column table is checked to realise the genuine branch of (D-a)/(D-b); and the
`H(20)` boundary instance on `ℤ₂×ℤ₂` with `K` the diagonal subgroup — with
`HadamardExists 52` and `HadamardExists 20` as corollaries. **No novelty of
existence is claimed at either order**; both are long settled. What the
instances do is instantiate the theorem.

## The definitional surface

Fifty-eight definitions are compared alongside the twenty-six theorems, which
is a large surface to select and a deliberate one. In a formalization of this
shape the definitions carry the content: `border` decides what a bordered array
*is*, `gsBlock` fixes the array's orientation down to six signs, `H1`--`H4` are
the hypotheses the whole characterisation quantifies over, and the instance
literals `seed52Data`, `E52`, `P52`, `Q52` and their order-20 counterparts are
the records themselves. An unchecked definition anywhere in that list would let
every theorem above be true of a different object. Each one carries a docstring
in `Challenge.lean` stating its intended value and, where it is not obvious,
which compared theorems constrain it; those docstrings are the per-definition
account, and the group above is the per-theorem one.

## The mathematics

The object is a border. A Goethals--Seidel array of four sequences developed
over a finite abelian group `G` is Hadamard exactly when their aggregate
periodic autocorrelation vanishes off the origin; bordering it with strips of
width `4s` relaxes that to a profile with a deficit on the border's account.
What Hadamard-B adds, and what Theorem A characterises, is a border whose
strips are **constant on the cosets of a proper subgroup** `K ≤ G` of index
`i ≥ 2` rather than on all of `G`. The characterisation is an iff, so it also
says what the ansatz *forces*: the diagonal `M(0) = 4s`, and — off the origin —
that the aggregate profile factors through `G/K`, because a `±1` Gram cannot
see anything finer than a coset. Theorem B names the house branch of the
admissible Gram tables. At `s = 1` the index-one and index-two systems turn out
to be the same `4 × 4` system with a different argument: Theorem D's genuine
branch reaches it by forcing the tables, its degenerate branch (D-a′) is the
index-one system written twice, the (D-e) transport moves borders between the
two exactly when `d = r`, and the character twist of Lemma T carries one seed
problem onto the other.

What is **not** here: Theorem C's forced-parameter clauses D1--D4 and the
classification corollary they support, which need rank and positive
semidefiniteness over `ℝ` and character orthogonality over `ℂ`; the
characteristic-subgroup and automorphism-equivariance clauses of the index-two
collapse corollary (§1.6); the 768² census behind (D-e), which is a Python
certificate in the source repository, not a theorem here; and the whole of the
source note's Movement III — the separation theorem at order 668 and the exact
4-profile invariants behind it. Those invariants are not formalized here; they
are outside this registration's scope, and impractical under direct kernel
reduction. For the full note, the twelve verified public records, the eight
certified instances, and the three-class theorem at order 668, see
[Hadamard-B](https://github.com/JD-Jones-ASES/Hadamard-B).

## Relation to previous formalisations

Mathlib at the pinned revision supplies the `Matrix.IsHadamard` predicate that
every conclusion here is stated in, together with the closure and
reconstruction lemmas the proofs use; it exhibits no Hadamard matrix of any
order, contains no existence theorem, and has no content on Goethals--Seidel
arrays, group-developed blocks, coset borders, or autocorrelation profiles.
Its `Matrix.circulant` module is the nearest existing object — the type-1
development used here is the transpose of a circulant — but carries nothing
about the block array.

The sibling repository
[Hadamard-formal](https://github.com/JD-Jones-ASES/Hadamard-formal) is the
ancestor of this one's developed-matrix algebra and its sixteen-block
Goethals--Seidel Gram lemma, ported with two changes: the six transposed blocks
are negated, because that repository uses the SageMath orientation while this
one uses the note's standard orientation, and the reflection is an arbitrary
shift `R_ρ` rather than the group inversion. The `s = 0` theorem here strictly
generalizes the sibling's, which is fixed at `ρ = 0`.

Two public Lean formalizations of a single Hadamard matrix of order 668 exist,
both built from the data posted publicly on 2026-08-12:
`Paul-Lez/hadamard-668-comparator` (Palomar entry PALOMAR-2026-08-17-000002),
whose `Challenge.lean` independently exhibits the bordered structure at that
order — circulants on `Fin 166`, a width-4 border, per-block-constant strips,
the same `4 × 4` corner — and `Arthur742Ramos/hadamard-668-lean`
(Ramos–Hulak–de Queiroz; Palomar entry
PALOMAR-2026-08-29-000009), which verifies one supplied matrix. Neither states
the general construction theorem or the classification; that is the sense in
which this repository is a distinct object, and the observation is the source
note's (NOTE-B §4.3).

## Data and proof boundary

The committed, standard-library-only `scripts/export_data.py` reads two JSON
records from a Hadamard-B checkout. Before parsing, it requires their bytes to
match the SHA-256 pins below; it then validates the record fields it depends on
and emits `HadamardBFormal/Data/Generated.lean` deterministically.

| Source at `Hadamard-B@01a7f0614208ca68d69e64a7cd5b560aadafbb8a` | SHA-256 |
| --- | --- |
| `data/h52-gate.json` | `ef60c4ff9f245eec5ba7f035e5968152836207fcd9235a0b1851150d2fb1d170` |
| `data/h20-boundary.json` | `716610543b79ab9e1c9f1adb142c114544e70e58d370500130b83c17a18cf254` |

The exporter enforces byte identity against the pins before emitting; it proves
no mathematical property of the data. Lean then checks the hypotheses of
Theorem A on the imported literals by ordinary kernel reduction — `decide`,
never `native_decide` — and the Hadamard conclusion is *derived* from the
theorem. Everything decided is `O(n²)` in the order of the group: for the gate
the profile check is `4 × 12 × 12 = 576` integer products, (H1) is 64 pairs of
length-4 dot products, (H3) is `4 × 4` and (H4) is `4 × 8`. **The assembled
`52 × 52` matrix and its `52³` product are never materialized.**

The exporter's index convention is not proved correct inside Lean, and a wrong
one would **not** necessarily turn the build red: at order 52 the reindexing
`(a,b,c) ↦ (a,b,−c)` preserves `κ` and leaves the profile check green, and at
order 20 so does the coordinate swap — each names a different matrix while
satisfying the same hypotheses. Three things are established, and they are not
the same thing:

- the kernel checks establish the **mathematical properties of the functions
  Lean receives**;
- the exporter's SHA-256 pins establish **which bytes were consumed**;
- **literal source-index fidelity** rests on convention review together with the
  independent cross-check `scripts/crosscheck_assembly.py`, which re-implements
  the index maps, the Goethals--Seidel block table and the border layout from
  `Challenge.lean` — not from the exporter — assembles both instance matrices,
  hands them to the source repository's own `verify/verify.py`, and requires the
  canonical digest it reports to equal the digest each record pins:

| Instance | canonical SHA-256, cross-checked against the record's `pinned_sha256` |
| --- | --- |
| `H(52)` gate | `e2c3e48b0fc65f5283e833096824b4fec651d8c57694ae45b3842c23c87ad7ca` |
| `H(20)` boundary T1 | `50eecc761e12b76944b301b7aaeb03a61cb6b88cfc52c67caaacf20eef0e6c9b` |

The same script also requires the literal tables inlined in `Challenge.lean` and
emitted into `HadamardBFormal/Data/Generated.lean` to equal the record's tables
entry for entry, so the compared statement surface demonstrably holds the
record's bytes.

The order-20 record carries two instances. Only T1 is exported: T2 declares the
transpose-negated orientation, this library formalizes the standard orientation
only, and the exporter refuses to emit it. Hadamard-B's Python certificates,
searches, and decode history are that repository's own replayable record and
are not re-proved here.

`Challenge.lean` is the Mathlib-only statement surface for Palomar and contains
only the deliberate proof holes that Comparator expects. `Solution.lean`
repeats those statements and connects them to the completed development under
`HadamardBFormal/`. The proof library and the solution have no proof holes.

## Sources and provenance

- `Hadamard-B@01a7f0614208ca68d69e64a7cd5b560aadafbb8a`, `note/NOTE-B.md`
  §§1.0--1.6 and §2.2, is the source for every statement formalized here and
  for the two pinned instance records. **That repository is public as of
  2026-09-01**, and the pinned commit resolves without authentication —
  verified the same day. The account given here is nonetheless self-contained,
  and nothing above asks the reader to take the note's word for what is
  proved. Claims about the source's own results — its certificates, its
  searches, its prior-art statements — rest on the source and are marked as
  such.
- The classical spine is credited in NOTE-B §4.1 from firsthand reads: the
  four-block array is Goethals--Seidel (1970); the general-abelian setting and
  the classical width-4 border are Wallis--Whiteman (1972), with Spence (1975)
  the even-order cyclic sibling; the compression device is
  Đoković--Kotsireas's.

Kernel replay, Comparator statement matching, and the axiom audit establish
proof replay and statement fidelity — not literature status, novelty, or the
source note's documentary claims.

**Production and review.** The mathematics, the Lean, the exporter and this
packaging were produced by AI systems — Claude Code (Fable 5, Anthropic) with
Claude Opus subagent lanes — with a human owner managing the workflow and making
no mathematical contribution. Two reviews have been performed, both by AI
systems, and **no independent human expert has reviewed the source rendering**.
`DISCLOSURE.md` gives the full work split, the review record and the credit
chain; `formalization.yaml` carries the same account under `automation` and
`review`.

## Reproduce

Lean 4 and Mathlib are pinned by `lean-toolchain` and `lake-manifest.json` at
`v4.33.0` — the newest Lean release with a matching
[lean4export](https://github.com/leanprover/lean4export) release, which
Palomar's export check requires. With Elan installed:

```powershell
lake exe cache get
python -B .\scripts\verify.py --source-root C:\GitHub_Files\Claude-Repos\Hadamard-B
```

`scripts/verify.py` is the single entrypoint: it runs `lake build`, the exporter
in `--check` mode, the assembly cross-check, a forbidden-token scan, and a
set-equality check tying `comparator.json`, `Test/AxiomAudit.lean`,
`Challenge.lean`, `Solution.lean` and `formalization.yaml` to the same
twenty-six theorem names and fifty-eight definition names. Any of them can be
run alone:

```powershell
lake build
python .\scripts\export_data.py --source-root <Hadamard-B checkout> --check
python .\scripts\crosscheck_assembly.py --source-root <Hadamard-B checkout>
```

For a portable checkout, replace the source path with the path to a Hadamard-B
checkout at the pinned commit. `lake build` also runs the transitive axiom audit
over the twenty-six public theorems; it rejects any dependency outside
`propext`, `Classical.choice`, and `Quot.sound`. Warnings caused by the
deliberate holes in `Challenge.lean` are expected — there are twenty-six of
them, one per compared theorem. Warnings or proof holes anywhere else are
regressions.

## License

The entire snapshot at the pinned commit — Lean sources, scripts, metadata
and prose alike — is licensed under the MIT License; see `LICENSE`. No
licence is claimed over the mathematical facts the instance data encodes;
the MIT grant covers the files that express them, which is a different
thing.
