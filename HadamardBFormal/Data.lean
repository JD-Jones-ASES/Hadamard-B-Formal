/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import HadamardBFormal.Data.Generated
import HadamardBFormal.TheoremD

/-!
# Kernel-checked facts about the `H(52)` gate instance

The literals in `HadamardBFormal.Data.Generated` are emitted by the committed,
hash-checking exporter `scripts/export_data.py`.  This module checks the
hypotheses of Theorem A on them with ordinary kernel reduction (`decide`, never
`native_decide`).

Everything decided here is `O(n²)` in the order of the group: the two-tier PAF
profile is `4 × 12 × 12 = 576` integer products, (H1) is `64` pairs of length-`4`
dot products, (H3) is `4 × 4` and (H4) is `4 × 8`.  **The assembled `52 × 52`
matrix and its `52³` product are never materialized** — the Hadamard conclusion
is *derived* from Theorem A in `HadamardBFormal/Results.lean`, not computed.

The index convention of the exporter is not proved correct inside Lean, and a
wrong one would **not** necessarily turn the build red: the reindexing
`(a,b,c) ↦ (a,b,−c)` preserves `κ` and leaves `h2_52` — the profile check —
green, and at order 20 so does the coordinate swap; each names a different
matrix satisfying the same hypotheses.  What the checks here establish is the
mathematical properties of the functions Lean receives; the exporter's SHA-256
pins establish which bytes were consumed; literal source-index fidelity rests on
convention review together with the independent cross-check
`scripts/crosscheck_assembly.py`, which reassembles both instances from
`Challenge.lean`'s semantics and requires the source repository's own canonical
digests.  `H1`--`H4` are `def`s rather than `abbrev`s, so each check unfolds its
hypothesis before handing the goal to `decide`.
-/

namespace HadamardBFormalCore.Data

open scoped BigOperators Matrix

open HadamardBFormalCore

/-! ### The group -/

set_option maxRecDepth 100000 in
/-- The gate group has order `12`, so the bordered array has order `4(12+1) = 52`. -/
theorem card_G52 : Fintype.card G52 = 12 := by decide

set_option maxRecDepth 100000 in
/-- The index-two character is onto. -/
theorem kappa52_surjective : Function.Surjective kappa52 := by decide

set_option maxRecDepth 100000 in
/-- Both fibers of `κ` have size `w = 6`. -/
theorem kappa52_fiber :
    ∀ c : ZMod 2, (Finset.univ.filter fun g : G52 => kappa52 g = c).card = 6 := by decide

/-- `κ ρ = 0`: the gate instance is the `ε = +1` branch of `NOTE-B` §1.5. -/
theorem kappa52_rho52 : kappa52 rho52 = 0 := rfl

/-! ### Sign-valuedness -/

-- The three border tables are `Matrix`-typed, and instance search does not find a
-- `Decidable` instance for a *nested* `∀` over the index types of a `Matrix`
-- (it does for the same statement about a plain function).  Quantifying over the
-- product of the two index types sidesteps that and decides identically.
set_option maxRecDepth 100000 in
theorem seed52_isSign : ∀ q g, IsSign (seed52 q g) := by decide

set_option maxRecDepth 100000 in
theorem E52_isSign : ∀ r c, IsSign (E52 r c) := by
  have h : ∀ z : Fin (4 * 1) × Fin (4 * 1), IsSign (E52 z.1 z.2) := by decide
  exact fun r c => h (r, c)

set_option maxRecDepth 100000 in
theorem P52_isSign : ∀ r z, IsSign (P52 r z) := by
  have h : ∀ y : Fin (4 * 1) × (Fin 4 × ZMod 2), IsSign (P52 y.1 y.2) := by decide
  exact fun r z => h (r, z)

set_option maxRecDepth 100000 in
theorem Q52_isSign : ∀ z c, IsSign (Q52 z c) := by
  have h : ∀ y : (Fin 4 × ZMod 2) × Fin (4 * 1), IsSign (Q52 y.1 y.2) := by decide
  exact fun z c => h (z, c)

/-! ### The hypotheses of Theorem A -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Sixty-four pairs of length-four dot products.
/-- **(H1)** `Q Qᵀ = I₄ ⊗ M` for the house Gram table `M = 8I₂ − 4J₂`. -/
theorem h1_52 : H1 (s := 1) Q52 (houseM 1) := by
  unfold H1
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The two-tier profile at every one of the eleven nonzero shifts:
-- `4 × 12 × 12 = 576` integer products.  This is the check that would catch a
-- wrong mixed-radix index convention in the exporter.
/-- **(H2)** the two-tier PAF profile `Σ PAF(t) = −M(κ t)` off the origin. -/
theorem h2_52 : H2 seed52 kappa52 (houseM 1) := by
  unfold H2
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- A `4 × 4` corner Gram plus a `4 × 8` row-table Gram; the heartbeat bump is the
-- same house incantation as the other kernel checks in this file.
/-- **(H3)** `E Eᵀ + w · P Pᵀ = N · I₄`, with `w = 6` and `N = 52`. -/
theorem h3_52 : H3 (s := 1) E52 P52 ((6 : ℕ) : ℤ) 52 := by
  unfold H3
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The compressed core is evaluated by kernel reduction of the coset sums; only
-- the `4 × 8` coupling matrix is ever formed.
/-- **(H4)** `E Qᵀ + P Ĉᵀ = 0`, with `Ĉ = GS(σ₀,…,σ₃; κρ)` the compressed core. -/
theorem h4_52 : H4 (s := 1) E52 P52 Q52 (chat kappa52 seed52 rho52) := by
  unfold H4
  decide

/-! ### The order-20 boundary instance

`NOTE-B` §2.2, cert 05: the `w = 2s` boundary, on `G = ZMod 2 × ZMod 2` with `K`
the **diagonal** subgroup.  `K` is not a coordinate kernel, which is exactly what
the surjective-hom model of the quotient buys: `κ(a,b) = a + b` and nothing else
changes. -/

set_option maxRecDepth 100000 in
/-- The boundary group has order `4`, so the bordered array has order `4(4+1) = 20`. -/
theorem card_G20 : Fintype.card G20 = 4 := by decide

set_option maxRecDepth 100000 in
theorem kappa20_surjective : Function.Surjective kappa20 := by decide

set_option maxRecDepth 100000 in
/-- Both fibers of the diagonal `κ` have size `w = 2` — the boundary `w = 2s`. -/
theorem kappa20_fiber :
    ∀ c : ZMod 2, (Finset.univ.filter fun g : G20 => kappa20 g = c).card = 2 := by decide

set_option maxRecDepth 100000 in
theorem seed20_isSign : ∀ q g, IsSign (seed20 q g) := by decide

set_option maxRecDepth 100000 in
theorem E20_isSign : ∀ r c, IsSign (E20 r c) := by
  have h : ∀ z : Fin (4 * 1) × Fin (4 * 1), IsSign (E20 z.1 z.2) := by decide
  exact fun r c => h (r, c)

set_option maxRecDepth 100000 in
theorem P20_isSign : ∀ r z, IsSign (P20 r z) := by
  have h : ∀ y : Fin (4 * 1) × (Fin 4 × ZMod 2), IsSign (P20 y.1 y.2) := by decide
  exact fun r z => h (r, z)

set_option maxRecDepth 100000 in
theorem Q20_isSign : ∀ z c, IsSign (Q20 z c) := by
  have h : ∀ y : (Fin 4 × ZMod 2) × Fin (4 * 1), IsSign (Q20 y.1 y.2) := by decide
  exact fun z c => h (z, c)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The same house incantation as the gate checks above.
theorem h1_20 : H1 (s := 1) Q20 (houseM 1) := by
  unfold H1
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- `4 × 4 × 4 = 64` integer products; the check that would catch a wrong index
-- convention or a wrong reading of the diagonal subgroup.
theorem h2_20 : H2 seed20 kappa20 (houseM 1) := by
  unfold H2
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- `w = 2` here: the hypothesis boundary `w = 2s` of `NOTE-B` §1.3, D3.
theorem h3_20 : H3 (s := 1) E20 P20 ((2 : ℕ) : ℤ) 20 := by
  unfold H3
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The compressed core over the diagonal quotient.
theorem h4_20 : H4 (s := 1) E20 P20 Q20 (chat kappa20 seed20 rho20) := by
  unfold H4
  decide

end HadamardBFormalCore.Data
