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

Besides the definitions the file carries the **mechanics** that every use of the
ansatz shares:

* `fromBlocks_eq_smul_one_iff` and `border_gram_iff` — the reduction of
  `H Hᵀ = N · I` to the four block equations displayed in `NOTE-B` §1.1;
* `rowStrip_mul_transpose` — `P̃ P̃ᵀ = w · P Pᵀ`, the top-left computation, for any
  quotient map whose fibers all have size `w`;
* `colStrip_mul_transpose_apply` — `(Q̃ Q̃ᵀ)[(I,g),(I',g')] = (Q Qᵀ)[(I,κg),(I',κg')]`;
* `border_isSign`.

Theorem A itself is a later stage.
-/

namespace HadamardBFormalCore

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

/-! ### The four-block reduction of `H Hᵀ = N · I`

`NOTE-B` §1.1 displays `H Hᵀ` as a two-by-two array of blocks and reads off four
equations.  These two lemmas are that display, and they are what every stage of
the development consumes. -/

/-- A block matrix is a scalar multiple of the identity exactly when its diagonal
blocks are and its off-diagonal blocks vanish. -/
theorem fromBlocks_eq_smul_one_iff {m n : Type*} [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℤ) (B : Matrix m n ℤ) (C : Matrix n m ℤ) (D : Matrix n n ℤ) (N : ℤ) :
    Matrix.fromBlocks A B C D = N • (1 : Matrix (m ⊕ n) (m ⊕ n) ℤ) ↔
      A = N • 1 ∧ B = 0 ∧ C = 0 ∧ D = N • 1 := by
  rw [show (N • (1 : Matrix (m ⊕ n) (m ⊕ n) ℤ)) = Matrix.fromBlocks (N • 1) 0 0 (N • 1) by
      rw [← Matrix.fromBlocks_one (l := m) (m := n), Matrix.fromBlocks_smul, smul_zero,
        smul_zero],
    Matrix.fromBlocks_inj]

/-- The Gram of the bordered array, in block form.  This is the display

```
H Hᵀ = [ E Eᵀ + P̃ P̃ᵀ      E Q̃ᵀ + P̃ Cᵀ ]
       [ Q̃ Eᵀ + C P̃ᵀ      Q̃ Q̃ᵀ + C Cᵀ ]
```
-/
theorem border_mul_transpose [AddCommGroup G] [Fintype G] [AddCommGroup Gbar]
    {s : ℕ} (κ : G →+ Gbar)
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G) :
    border κ E P Q x ρ * (border κ E P Q x ρ).transpose =
      Matrix.fromBlocks
        (E * E.transpose + rowStrip κ P * (rowStrip κ P).transpose)
        (E * (colStrip κ Q).transpose + rowStrip κ P * (core x ρ).transpose)
        (colStrip κ Q * E.transpose + core x ρ * (rowStrip κ P).transpose)
        (colStrip κ Q * (colStrip κ Q).transpose + core x ρ * (core x ρ).transpose) := by
  rw [border, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]

/-- **The four block equations of `NOTE-B` §1.1.**  The bordered array has Gram
`N · I` exactly when the top-left block is `N · I`, the top-right and bottom-left
blocks vanish, and the bottom-right block is `N · I`. -/
theorem border_gram_iff [AddCommGroup G] [Fintype G] [DecidableEq G] [AddCommGroup Gbar]
    {s : ℕ} (κ : G →+ Gbar)
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G) (N : ℤ) :
    border κ E P Q x ρ * (border κ E P Q x ρ).transpose = N • 1 ↔
      (E * E.transpose + rowStrip κ P * (rowStrip κ P).transpose = N • 1) ∧
        (E * (colStrip κ Q).transpose + rowStrip κ P * (core x ρ).transpose = 0) ∧
        (colStrip κ Q * E.transpose + core x ρ * (rowStrip κ P).transpose = 0) ∧
        (colStrip κ Q * (colStrip κ Q).transpose
          + core x ρ * (core x ρ).transpose = N • 1) := by
  rw [border_mul_transpose, fromBlocks_eq_smul_one_iff]

/-! ### The two strips -/

/-- Summing a function of the quotient over the group multiplies it by the common
fiber size.  This is the only aggregation device the development uses. -/
theorem sum_comp_of_card_fiber_eq [Fintype G] [Fintype Gbar] [DecidableEq Gbar] {w : ℕ}
    (κ : G → Gbar)
    (hw : ∀ c : Gbar, (Finset.univ.filter fun g : G => κ g = c).card = w) (F : Gbar → ℤ) :
    (∑ g : G, F (κ g)) = (w : ℤ) * ∑ c, F c := by
  rw [← Finset.sum_fiberwise' Finset.univ κ F, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_const, hw c, nsmul_eq_mul]

/-- **The top-left computation.**  Each class `(J,c)` has exactly `w` members, so
`P̃ P̃ᵀ = w · P Pᵀ`. -/
theorem rowStrip_mul_transpose [Fintype G] [Fintype Gbar] [DecidableEq Gbar] {s w : ℕ}
    (κ : G → Gbar)
    (hw : ∀ c : Gbar, (Finset.univ.filter fun g : G => κ g = c).card = w)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ) :
    rowStrip κ P * (rowStrip κ P).transpose = (w : ℤ) • (P * P.transpose) := by
  ext r r'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowStrip_apply, Matrix.smul_apply,
    smul_eq_mul, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  exact sum_comp_of_card_fiber_eq κ hw fun c => P r (J, c) * P r' (J, c)

/-- **The bottom-right computation, first half.**  The column strip repeats the
rows of `Q` along the fibers, so its Gram is `Q Qᵀ` read at the images. -/
theorem colStrip_mul_transpose_apply {s : ℕ} (κ : G → Gbar)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ) (z z' : Fin 4 × G) :
    (colStrip κ Q * (colStrip κ Q).transpose) z z' =
      (Q * Q.transpose) (z.1, κ z.2) (z'.1, κ z'.2) :=
  rfl

/-! ### Signs -/

/-- The bordered array of sign-valued data is sign valued. -/
theorem border_isSign [AddCommGroup G] [AddCommGroup Gbar] {s : ℕ} (κ : G →+ Gbar)
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G)
    (hE : ∀ r c, IsSign (E r c)) (hP : ∀ r z, IsSign (P r z))
    (hQ : ∀ z c, IsSign (Q z c)) (hx : ∀ q g, IsSign (x q g))
    (i j : Fin (4 * s) ⊕ (Fin 4 × G)) : IsSign (border κ E P Q x ρ i j) := by
  cases i with
  | inl r =>
    cases j with
    | inl c => exact hE r c
    | inr z => exact hP r _
  | inr z =>
    cases j with
    | inl c => exact hQ _ c
    | inr y => exact core_isSign x ρ hx z y

end HadamardBFormalCore
