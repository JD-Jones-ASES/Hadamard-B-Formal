# Disclosure

The result is a Lean 4 / Mathlib formalization of part of the theorem layer of
Hadamard-B: twenty-six compared theorems over fifty-eight compared definitions.
They are the exact characterisation of the coset-border extension of a
Goethals–Seidel array over a finite abelian group (Theorem A, an iff); its house
form and the two classical degenerations it contains (Theorem B); the two
row-sum rows D5 and D6 of Theorem C, and only those two; the character-twist
layer of Lemma T and the `ψ(ρ) = 1` conjugation; Theorem D's clauses (D-a)
through (D-e), including the degenerate-branch collapse (D-a′) with its
entry-for-entry `H = H₁` equality and its converse, and both directions of the
(D-e) transport, packaged as the note's *exactly when*; the seed-problem
bijection clause of §1.6, and only that clause — together with two witness
records checked in the kernel against the hypotheses of Theorem A, which carry
Hadamard matrices of orders 52 and 20 through the theorem.

On the compared surface this is a complete resolution of the `s = 1`, `i = 2`
border system in the sense of Theorem D's own clauses. Two exclusions belong in
the same breath: §1.6's characteristic-subgroup and automorphism-equivariance
clauses are not formalized, and neither is the 768² census behind (D-e), which
is a Python certificate in the source repository. Theorem C's forced-parameter
clauses D1–D4 and the classification corollary are not formalized either.

**No novelty of existence is claimed at order 52 or order 20.** Both orders are
long settled. The instances exist to instantiate the theorem: the gate record
is a from-scratch index-two instance on a non-cyclic group in the branch the
decoded public records do not exercise, and the order-20 record sits on the
`w = 2s` hypothesis boundary with an arbitrary index-two subgroup rather than a
coordinate kernel.

AI-generated formalization with a human managing the workflow. Produced by
Claude Code (Fable 5, Anthropic) with Claude Opus subagent lanes: a planning
lane read the source note and the pinned Mathlib tree and produced a
source-controlled pour plan; staged implementation lanes poured the library in
that order, each stage gated on a green build; an adversarial audit lane
reviewed the statements against the note.

## What the AI stations did

Everything mathematical and everything in Lean. The Lean statements and their
proofs; the choice of proof routes, including the integer route through
Theorem D that replaces the source note's rank and positive-semidefiniteness
argument; the deterministic hash-checking exporter; the Palomar packaging and
this metadata; and the audits.

## What the human owner did

Granted the sessions, paid for the compute, supplied the source repository,
ruled the compared surface, and rules on licensing, publication, and any
Palomar submission. No mathematical contribution, and none is claimed. The
owner's name appears here, in the copyright line, and in the citation metadata;
it appears in no derivation.

## Review

Two reviews have been performed, **both by AI systems**:

- **Claude (Anthropic), statement-fidelity audit lane, 2026-09-01** — audited
  the Lean statements against the source note's current text and produced the
  divergence list in `formalization.yaml` under `fidelity.divergences`.
- **GPT 5.6 (OpenAI, Codex desk), independent package review, 2026-09-01** —
  independently rebuilt the package from an isolated checkout with the pinned
  toolchain, replayed the transitive axiom audit and the exporter check, and
  reviewed the publication surface.

**No independent human expert review has occurred.** `review.status` in
`formalization.yaml` is `agent-reviewed` and names those two systems. JD Jones
is the responsible owner, publisher and maintainer; he is not listed as a
reviewer, because the review work was not his.

## What is independently checked here

There are four distinct layers, and they are not the same layer.

1. Hadamard-B carries the prose proofs, the Python certificates, the decode of
   the publicly posted records, and the exact-integer verification of its own
   results. **None of that is imported as proof.** Its theorems are labelled
   PROVEN (paper-grade) there; what this repository adds is that the sanctioned
   tranche of them is now machine-checked.
2. `scripts/export_data.py` authenticates the two selected Hadamard-B JSON
   records by SHA-256 before parsing, checks the record fields the Lean
   encoding depends on, and translates the literals deterministically. This
   establishes byte identity and deterministic decoding — not any mathematical
   property of the data, and not by itself the index convention.
3. `scripts/crosscheck_assembly.py` closes that last gap independently of the
   exporter. A wrong index convention would **not** necessarily go red: at
   order 52 the reindexing `(a,b,c) ↦ (a,b,−c)` preserves `κ` and leaves the
   profile check green, and at order 20 so does the coordinate swap. The
   cross-check re-implements the index maps, the block table and the border
   layout from `Challenge.lean`, assembles both matrices, and requires the
   canonical digest reported by the source repository's own `verify/verify.py`
   to equal the digest each record pins — `e2c3e48b…` at order 52,
   `50eecc76…` at order 20. It also requires the literals inlined in
   `Challenge.lean` and generated into `HadamardBFormal/Data/Generated.lean` to
   equal the record's tables entry for entry.
4. Lean checks the hypotheses of Theorem A on the translated literals by
   ordinary kernel reduction and then *derives* the Hadamard conclusion from
   the theorem. `native_decide` is not used anywhere. No assembled matrix is
   accepted because a source script accepted it; the `52 × 52` array and its
   `52³` product are never formed.

The axiom audit is transitive and runs at build time over all twenty-six public
theorems; it permits only `propext`, `Classical.choice`, and `Quot.sound`. The
proof library and `Solution.lean` contain no proof holes; the only `sorry`s are
the twenty-six deliberate holes in `Challenge.lean`, one per compared theorem,
which is what Palomar's Comparator expects. `scripts/verify.py` runs the whole
set and additionally checks that the theorem and definition lists in
`comparator.json`, `Test/AxiomAudit.lean`, `Challenge.lean`, `Solution.lean` and
`formalization.yaml` are set-equal, so those five lists cannot drift apart
silently.

**Local versus protected.** The local build, the transitive axiom audit, the
exporter check and the assembly cross-check have been run and pass. A successful
Palomar protected run **would additionally** establish agreement between the
recorded Challenge and the recorded Solution through Comparator, and replay of
the exported proof through Lean's kernel and the pinned NanoDa kernel. Neither
that run nor anything above establishes fidelity to the informal source,
novelty, interest, or peer review. No Comparator, `lean4export` or NanoDa
tooling has been run against this repository, and none is installed on the
machine that built it.

**Statement fidelity.** Comparator matching, when it runs, will show that the
solved statements are the challenge statements; it will not show that either is
a faithful rendering of the source note. That rendering was audited by an AI
lane against the note's current text and **was not reviewed by an independent
human expert**. The deliberate departures are listed in `formalization.yaml`
under `fidelity.divergences`; the load-bearing ones are that every statement is
for the note's standard orientation only, that the quotient `G/K` is modelled as
a surjective additive hom rather than a quotient type, that Theorem C is
represented only by D5 and D6, that several statements drop ambient hypotheses
in the strengthening direction — including that `twist_profile_iff` and
`collapse_seedProblem_bijection` accept any `κ : G →+ ZMod 2`, surjective or
not — and that the §1.6 corollary is represented only by its seed-problem
bijection clause.

## Formal scope

Lean proves mathematical statements about arbitrary finite abelian groups and
about the two pinned witness records. It does not establish the provenance of
those records, the search history behind them, the source note's prior-art and
credit statements, or anything in the note's Movement III — the separation
theorem at order 668 rests on exact 4-profile computations that are not
formalized here, are outside this registration's scope, and are impractical
under direct kernel reduction; they are Hadamard-B's certificates, not theorems
here.

The mathematical source repository is **private at the time of writing** and is
expected to be public at registration. Until it is, a reader cannot inspect the
note at its pinned SHA. The account in `README.md` is written to be
self-contained for that reason: every compared theorem has a plain-language
statement there and every compared definition a docstring in `Challenge.lean`,
so the exact claim can be identified and assessed without reaching the source.

## Credit for external mathematics and data

- `Hadamard-B@d460202cbc1f30e3a48c28fad916cac00d87cf30`, `note/NOTE-B.md`
  §§1.0–1.6 and §2.2, supplies every statement formalized here and the two
  instance records.
- The full credit chain, with the sources read firsthand and the one bounded
  novelty statement, is `note/NOTE-B.md` §4. In brief: the four-block array is
  Goethals–Seidel (1970); the general-abelian setting and the classical width-4
  border are Wallis–Whiteman (1972), with Spence (1975) the even-order cyclic
  sibling; the compression device is Đoković–Kotsireas's.
- The developed-matrix algebra and the sixteen-block Gram lemma are ported from
  the sibling repository Hadamard-formal, in the opposite array orientation.

## License

The entire snapshot at the pinned commit — Lean sources, scripts, metadata
and prose alike — is licensed under the MIT License; see `LICENSE`. No
licence is claimed over the mathematical facts the instance data encodes.
