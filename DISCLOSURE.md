# Disclosure

The result is a Lean 4 / Mathlib formalization of the theorem layer of
Hadamard-B: the exact characterisation of the coset-border extension of a
Goethals–Seidel array over a finite abelian group (Theorem A), its house form
and the two classical degenerations it contains (Theorem B), the two row-sum
rows D5 and D6, the character-twist layer of Lemma T and the `ψ(ρ) = 1`
conjugation, the complete resolution of the `s = 1`, index-two border system
(Theorem D), and the index-two seed-problem collapse — together with two
witness records checked in the kernel against the hypotheses of Theorem A,
which carry Hadamard matrices of orders 52 and 20 through the theorem.

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

## What is independently checked here

There are three distinct layers, and they are not the same layer.

1. Hadamard-B carries the prose proofs, the Python certificates, the decode of
   the publicly posted records, and the exact-integer verification of its own
   results. **None of that is imported as proof.** Its theorems are labelled
   PROVEN (paper-grade) there; what this repository adds is that the sanctioned
   tranche of them is now machine-checked.
2. `scripts/export_data.py` authenticates the two selected Hadamard-B JSON
   records by SHA-256 before parsing, checks the record fields the Lean
   encoding depends on, and translates the literals deterministically. This
   establishes byte identity and faithful decoding — not any mathematical
   property of the data. The exporter's index convention is deliberately not
   proved correct: if it were wrong, the kernel check of the two-tier profile
   would fail and the build would go red.
3. Lean checks the hypotheses of Theorem A on the translated literals by
   ordinary kernel reduction and then *derives* the Hadamard conclusion from
   the theorem. `native_decide` is not used anywhere. No assembled matrix is
   accepted because a source script accepted it; the `52 × 52` array and its
   `52³` product are never formed.

The axiom audit is transitive and runs at build time over all twenty-two public
theorems; it permits only `propext`, `Classical.choice`, and `Quot.sound`. The
proof library and `Solution.lean` contain no proof holes; the only `sorry`s are
the twenty-two deliberate holes in `Challenge.lean`, one per compared theorem,
which is what Palomar's Comparator expects.

**Statement fidelity.** Comparator matching shows that the solved statements
are the challenge statements; it does not show that either is a faithful
rendering of the source note. That rendering was audited by an AI lane against
the note's current text and **was not reviewed by an independent human
expert**. The deliberate departures are listed in `formalization.yaml` under
`fidelity.divergences`; the load-bearing ones are that every statement is for
the note's standard orientation only, that the quotient `G/K` is modelled as a
surjective additive hom rather than a quotient type, that Theorem C is
represented only by D5 and D6, that clause (D-a′) of Theorem D is not
formalized, and that the transport clause takes the note's condition `d = r` as
an explicit hypothesis.

## Formal scope

Lean proves mathematical statements about arbitrary finite abelian groups and
about the two pinned witness records. It does not establish the provenance of
those records, the search history behind them, the source note's prior-art and
credit statements, or anything in the note's Movement III — the separation
theorem at order 668 rests on exact 4-profile computations that are outside
kernel reach and are Hadamard-B's certificates, not theorems here.

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

Code is licensed under the MIT License; see `LICENSE`. The prose documents are
CC BY-SA 4.0; see `LICENSE-DOCS.md`.
