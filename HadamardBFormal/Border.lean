/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import HadamardBFormal.GS

/-!
# The border ansatz and the hypotheses (H1)--(H4)

`NOTE-B` §1.0--§1.1.  The quotient `Ḡ = G/K` is modelled as a **surjective
additive hom** `κ : G →+ Gbar` rather than as a quotient type; `K = ker κ`,
`i = card Gbar`, `w = card K`.  The border tables are indexed by `Fin 4 × Gbar`
rather than by `Fin (4 * i)`, which removes every `i * J + κ h` arithmetic
obligation and makes the compressed core `Ĉ` literally a `core` over `Gbar`.

```
H = [ E   P̃ ]      P̃[r, (J,h)] = P[r][(J, κ h)]
    [ Q̃   C ]      Q̃[(I,g), c] = Q[(I, κ g)][c]
```

Only the definitions live in this file; Theorem A is a later stage.
-/

namespace HadamardBFormal

open scoped BigOperators Matrix

variable {G Gbar : Type*}

/-- The row strip `P̃[r,(J,h)] = P[r][(J, κ h)]`: constant on each `K`-coset inside
each superblock. -/
def rowStrip {s : ℕ} (κ : G → Gbar) (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ) :
    Matrix (Fin (4 * s)) (Fin 4 × G) ℤ :=
  fun r z => P r (z.1, κ z.2)

@[simp]
theorem rowStrip_apply {s : ℕ} (κ : G → Gbar) (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (r : Fin (4 * s)) (z : Fin 4 × G) : rowStrip κ P r z = P r (z.1, κ z.2) :=
  rfl

/-- The column strip `Q̃[(I,g),c] = Q[(I, κ g)][c]`. -/
def colStrip {s : ℕ} (κ : G → Gbar) (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ) :
    Matrix (Fin 4 × G) (Fin (4 * s)) ℤ :=
  fun z c => Q (z.1, κ z.2) c

@[simp]
theorem colStrip_apply {s : ℕ} (κ : G → Gbar) (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (z : Fin 4 × G) (c : Fin (4 * s)) : colStrip κ Q z c = Q (z.1, κ z.2) c :=
  rfl

/-- The compressed core `Ĉ = GS(σ₀,σ₁,σ₂,σ₃; κ ρ)`: the Goethals--Seidel array of
the coset sums over the quotient group. -/
def chat [Fintype G] [AddCommGroup G] [AddCommGroup Gbar] [DecidableEq Gbar]
    (κ : G →+ Gbar) (x : Fin 4 → G → ℤ) (ρ : G) : Matrix (Fin 4 × Gbar) (Fin 4 × Gbar) ℤ :=
  core (fun q => cosetSum κ (x q)) (κ ρ)

/-- The bordered array `H = [[E, P̃],[Q̃, C]]`. -/
def border [AddCommGroup G] [AddCommGroup Gbar] {s : ℕ} (κ : G →+ Gbar)
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G) :
    Matrix (Fin (4 * s) ⊕ (Fin 4 × G)) (Fin (4 * s) ⊕ (Fin 4 × G)) ℤ :=
  Matrix.fromBlocks E (rowStrip κ P) (colStrip κ Q) (core x ρ)

/-- **(H1)** `Q Qᵀ = I₄ ⊗ M` with `M` a `Gbar`-invariant table. -/
def H1 {s : ℕ} [AddCommGroup Gbar] (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (M : Gbar → ℤ) : Prop :=
  ∀ a b : Fin 4 × Gbar, (∑ c, Q a c * Q b c) = if a.1 = b.1 then M (a.2 - b.2) else 0

/-- **(H2)** `Σ PAF(t) = -M (κ t)` off the origin. -/
def H2 [Fintype G] [AddCommGroup G] [AddCommGroup Gbar] (x : Fin 4 → G → ℤ) (κ : G →+ Gbar)
    (M : Gbar → ℤ) : Prop :=
  ∀ t : G, t ≠ 0 → sumPaf x t = -M (κ t)

/-- **(H3)** `E Eᵀ + w · P Pᵀ = N · I`. -/
def H3 {s : ℕ} [Fintype Gbar] [DecidableEq Gbar]
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ) (w N : ℤ) : Prop :=
  E * E.transpose + w • (P * P.transpose) = N • 1

/-- **(H4)** `E Qᵀ + P Ĉᵀ = 0`. -/
def H4 {s : ℕ} [Fintype Gbar] [DecidableEq Gbar]
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (Chat : Matrix (Fin 4 × Gbar) (Fin 4 × Gbar) ℤ) : Prop :=
  E * Q.transpose + P * Chat.transpose = 0

end HadamardBFormal
