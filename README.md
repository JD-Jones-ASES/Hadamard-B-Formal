# hadamard-b-formal

A Lean 4 / Mathlib formalization of the theorem layer of Hadamard-B: an exact
characterisation of when a Goethals--Seidel array over a finite abelian group
extends to a Hadamard matrix through a border whose strips are constant on the
cosets of a subgroup, the house form of that characterisation and its two
classical degenerations, the character-twist layer, the complete resolution of
the `s = 1`, index-two border system, and two kernel-checked instances taken
through the theorem rather than through a matrix product. All public theorems
are kernel-checked on Lean's three standard axioms.

## Registry

Registration pending; this section is completed at registration.

## What Lean proves

- **Theorem A**, both directions: with `κ : G →+ Ḡ` a surjective hom all of
  whose fibers have size `w`, sign-valued corner `E`, border tables `P`, `Q`
  and seeds `x`, the bordered array `H = [[E, P̃], [Q̃, C]]` is a Hadamard
  matrix of order `N = 4(|G| + s)` **if and only if** (H1) `Q Qᵀ = I₄ ⊗ M` for
  some `M : Ḡ → ℤ`, (H2) `Σ PAF(t) = −M(κ t)` off the origin, (H3)
  `E Eᵀ + w · P Pᵀ = N · I`, and (H4) `E Qᵀ + P Ĉᵀ = 0` against the compressed
  core. The sufficiency half is stated separately, without surjectivity.
- **Theorem B**: for the house Gram table, (H2) *is* the two-tier
  autocorrelation profile `4n·δ₀ − 4s·[t ∈ K∖0] + 4·[t ∉ K]`.
- The two classical degenerations, each at an **arbitrary** reflection shift
  `ρ` rather than only the group inversion: the Goethals--Seidel theorem over
  an arbitrary finite abelian group (`s = 0`), and the Wallis--Whiteman /
  Spence bordered construction (`s = 1`, `i = 1`).
- **D5** and **D6**: summing the house profile over `G` gives
  `Σ_q r_q² = 8n − 4w(s+1) + 4s`, and at index one non-negativity gives
  `n(s−1) ≤ s`.
- **Lemma T** — `PAF_{ψx}(t) = ψ(t)·PAF_x(t)` for a `±1`-valued character —
  the `s = 1` profile bijection it drives, and the proposition that a twist
  with `ψ(ρ) = 1` is a diagonal conjugation, hence manufactures no new matrix.
- **Theorem D**, the `s = 1`, `i = 2` border system: the Gram table is forced
  to `M(0) = 4`, `M(1) = ±4`, and in the genuine branch the column table
  pair-negates onto a `4 × 4` Hadamard matrix; the row table is then forced to
  pair-negate and both it and the corner are Hadamard; (H4) collapses to the
  single `4 × 4` equation `4·E = −p·Λ(d)ᵀ·U`; `Σ_q δ_q² = 4`; and an index-one
  border transports across the doubling to a valid index-two border.
- The **index-two collapse**: the character twist is an involution, a
  bijection of sign-valued quadruples, and a bijection carrying the
  `s = 1, i = 1` seed problem onto the `s = 1, i = 2` seed problem. It is a
  bijection of *seed problems*, not of matrices.
- Two instances through the theorem: the `H(52)` Theorem-D gate on the
  non-cyclic group `ℤ₂×ℤ₂×ℤ₃` in the `ε = +1` branch, and the `H(20)`
  boundary instance on `ℤ₂×ℤ₂` with `K` the diagonal subgroup — with
  `HadamardExists 52` and `HadamardExists 20` as corollaries. **No novelty of
  existence is claimed at either order**; both are long settled. What the
  instances do is instantiate the theorem.

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
admissible Gram tables; Theorem D closes the `s = 1` layer, where the index-one
and index-two systems turn out to be the same `4 × 4` system with a different
argument, and the character twist of Lemma T carries one seed problem onto the
other.

What is **not** here: Theorem C's forced-parameter clauses D1--D4 and the
classification corollary they support, which need rank and positive
semidefiniteness over `ℝ` and character orthogonality over `ℂ`; clause (D-a′),
the collapse of the degenerate Gram branch; the automorphism-equivariance
upgrade of the index-two collapse; and the whole of the source note's Movement
III — the separation theorem at order 668 and the exact 4-profile invariants
behind it, which are categorically outside kernel reach. For the full note, the
twelve verified public records, the eight certified instances, and the
three-class theorem at order 668, see
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
the same `4 × 4` corner — and `Arthur742Ramos/hadamard-668-lean` (Palomar entry
PALOMAR-2026-08-29-000009), which verifies one supplied matrix. Neither states
the general construction theorem or the classification; that is the sense in
which this repository is a distinct object, and the observation is the source
note's (NOTE-B §4.3).

## Data and proof boundary

The committed, standard-library-only `scripts/export_data.py` reads two JSON
records from a Hadamard-B checkout. Before parsing, it requires their bytes to
match the SHA-256 pins below; it then validates the record fields it depends on
and emits `HadamardBFormal/Data/Generated.lean` deterministically.

| Source at `Hadamard-B@d460202cbc1f30e3a48c28fad916cac00d87cf30` | SHA-256 |
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
`52 × 52` matrix and its `52³` product are never materialized.** The exporter's
index convention is deliberately not proved correct: a wrong mixed-radix order
would make the profile check fail and the build would go red.

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

- `Hadamard-B@d460202cbc1f30e3a48c28fad916cac00d87cf30`, `note/NOTE-B.md`
  §§1.1--1.6 and §2.2, is the source for every statement formalized here and
  for the two pinned instance records.
- The classical spine is credited in NOTE-B §4.1 from firsthand reads: the
  four-block array is Goethals--Seidel (1970); the general-abelian setting and
  the classical width-4 border are Wallis--Whiteman (1972), with Spence (1975)
  the even-order cyclic sibling; the compression device is
  Đoković--Kotsireas's.

Kernel replay, Comparator statement matching, and the axiom audit establish
proof replay and statement fidelity — not literature status, novelty, or the
source note's documentary claims. See `DISCLOSURE.md` for the human/AI work
split and the credit chain.

## Reproduce

Lean 4 and Mathlib are pinned by `lean-toolchain` and `lake-manifest.json` at
`v4.33.0` — the newest Lean release with a matching
[lean4export](https://github.com/leanprover/lean4export) release, which
Palomar's export check requires. With Elan installed:

```powershell
lake exe cache get
lake build
python .\scripts\export_data.py `
  --source-root C:\GitHub_Files\Claude-Repos\Hadamard-B `
  --check
```

For a portable checkout, replace the final source path with the path to a
Hadamard-B checkout at the pinned commit. `lake build` also runs the transitive
axiom audit over the twenty-two public theorems; it rejects any dependency
outside `propext`, `Classical.choice`, and `Quot.sound`. Warnings caused by the
deliberate holes in `Challenge.lean` are expected — there are twenty-two of
them, one per compared theorem. Warnings or proof holes anywhere else are
regressions.

Code is licensed under the MIT License; see `LICENSE`. The prose documents are
CC BY-SA 4.0; see `LICENSE-DOCS.md`.
