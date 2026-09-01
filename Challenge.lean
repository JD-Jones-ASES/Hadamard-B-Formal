import Mathlib

/-!
# Bordered Goethals--Seidel arrays: the public challenge

The challenge asks for the mathematics of `NOTE-B` §1: an exact
characterisation of when a Goethals--Seidel array over a finite abelian group
extends to a Hadamard matrix through a **coset border** of width `4s` (Theorem
A), the house form of that characterisation and its two classical
degenerations (Theorem B), the character-twist layer (Lemma T and the
`ψ(ρ) = 1` conjugation), the complete resolution of the `s = 1, i = 2` border
system (Theorem D), the index-two seed-problem collapse, and two
kernel-checkable instances of the theorem at orders `52` and `20`.

No novelty of existence is claimed at orders `52` or `20` — both are long
settled.  What the instance statements say is that the *theorem* carries them:
the Hadamard property of a `52 × 52` array is deduced from hypotheses checked
on a group of order `12`.

The challenge deliberately imports only Mathlib; the proof holes below are the
problem to be solved.
-/

namespace HadamardBFormal

open scoped BigOperators Matrix

/-! ## Signs and Hadamard matrices -/

/-- An integer is a Hadamard sign when it is `+1` or `-1`. -/
def IsSign (z : ℤ) : Prop :=
  z = 1 ∨ z = -1

/-- There exists a classical integer Hadamard matrix of order `n`. -/
def HadamardExists (n : ℕ) : Prop :=
  ∃ H : Matrix (Fin n) (Fin n) ℤ, H.IsHadamard

/-! ## Development, reflection, column reversal (`NOTE-B` §1.0) -/

/-- The type-1 development of a sequence: `dev(x)[g,h] = x (h - g)`. -/
def dev {G : Type*} [Sub G] (x : G → ℤ) : Matrix G G ℤ :=
  fun g h => x (h - g)

/-- The reflection `R_ρ : k ↦ ρ - k`, an involutive permutation of `G`.

`NOTE-B` §1.0 writes the permutation matrix as `R[k,h] = [k + h = ρ]`; acting
on columns it is `revCols (reflect ρ)`. -/
def reflect {G : Type*} [AddCommGroup G] (ρ : G) : Equiv.Perm G :=
  Equiv.subLeft ρ

/-- Reverse the columns of a square matrix along a permutation:
`(A R)[g,h] = A[g, r h]`. -/
def revCols {G : Type*} (r : Equiv.Perm G) (A : Matrix G G ℤ) : Matrix G G ℤ :=
  fun g h => A g (r h)

/-! ## Correlations and coset sums (`NOTE-B` §1.0) -/

/-- Periodic autocorrelation, `PAF_x(t) = ∑_u x u * x (u + t)`. -/
def paf {G : Type*} [Fintype G] [Add G] (x : G → ℤ) (t : G) : ℤ :=
  ∑ u, x u * x (u + t)

/-- The aggregate periodic autocorrelation of a quadruple, `Σ PAF(t)`. -/
def sumPaf {G : Type*} [Fintype G] [Add G] (x : Fin 4 → G → ℤ) (t : G) : ℤ :=
  ∑ q, paf (x q) t

/-- The coset sum `σ(c) = ∑_{κ g = c} x g`. -/
def cosetSum {G Gbar : Type*} [Fintype G] [DecidableEq Gbar] (κ : G → Gbar) (x : G → ℤ)
    (c : Gbar) : ℤ :=
  ∑ g with κ g = c, x g

/-! ## The Goethals--Seidel core, standard orientation (`NOTE-B` §1.0) -/

/-- The four-by-four table of blocks of the Goethals--Seidel array, in the
**standard** orientation of `NOTE-B` §1.0:

```
       [  A     BR     CR     DR  ]
       [ -BR     A    DᵀR   -CᵀR  ]        A = dev x₀, B = dev x₁,
       [ -CR   -DᵀR    A     BᵀR  ]        C = dev x₂, D = dev x₃
       [ -DR    CᵀR  -BᵀR     A   ]
```

Negating the six transposed blocks gives the other valid orientation (used,
e.g., by SageMath); every statement here is about the standard one. -/
def gsBlock {G : Type*} (r : Equiv.Perm G) (X : Fin 4 → Matrix G G ℤ) :
    Fin 4 → Fin 4 → Matrix G G ℤ :=
  ![
    ![X 0, revCols r (X 1), revCols r (X 2), revCols r (X 3)],
    ![-revCols r (X 1), X 0, revCols r ((X 3).transpose), -revCols r ((X 2).transpose)],
    ![-revCols r (X 2), -revCols r ((X 3).transpose), X 0, revCols r ((X 1).transpose)],
    ![-revCols r (X 3), revCols r ((X 2).transpose), -revCols r ((X 1).transpose), X 0]
  ]

/-- The Goethals--Seidel array as one matrix indexed by `Fin 4 × G`. -/
def gs {G : Type*} (r : Equiv.Perm G) (X : Fin 4 → Matrix G G ℤ) :
    Matrix (Fin 4 × G) (Fin 4 × G) ℤ :=
  fun i j => gsBlock r X i.1 j.1 i.2 j.2

/-- The core `C = GS(x₀,x₁,x₂,x₃; ρ)` of a seed quadruple over an abelian
group. -/
def core {G : Type*} [AddCommGroup G] (x : Fin 4 → G → ℤ) (ρ : G) :
    Matrix (Fin 4 × G) (Fin 4 × G) ℤ :=
  gs (reflect ρ) fun q => dev (x q)

/-! ## The border ansatz (`NOTE-B` §1.0--§1.1)

The quotient `Ḡ = G/K` is modelled as a **surjective additive hom**
`κ : G →+ Gbar` rather than as a quotient type; `K = ker κ`, `i = card Gbar`,
`w = card K`.  The border tables are indexed by `Fin 4 × Gbar` rather than by
`Fin (4 * i)`, which removes every `i * J + κ h` arithmetic obligation and
makes the compressed core `Ĉ` literally a `core` over `Gbar`. -/

/-- The row strip `P̃[r,(J,h)] = P[r][(J, κ h)]`: constant on each `K`-coset
inside each superblock. -/
def rowStrip {G Gbar : Type*} {s : ℕ} (κ : G → Gbar)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ) :
    Matrix (Fin (4 * s)) (Fin 4 × G) ℤ :=
  fun r z => P r (z.1, κ z.2)

/-- The column strip `Q̃[(I,g),c] = Q[(I, κ g)][c]`. -/
def colStrip {G Gbar : Type*} {s : ℕ} (κ : G → Gbar)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ) :
    Matrix (Fin 4 × G) (Fin (4 * s)) ℤ :=
  fun z c => Q (z.1, κ z.2) c

/-- The compressed core `Ĉ = GS(σ₀,σ₁,σ₂,σ₃; κ ρ)`: the Goethals--Seidel array
of the coset sums over the quotient group. -/
def chat {G Gbar : Type*} [Fintype G] [AddCommGroup G] [AddCommGroup Gbar] [DecidableEq Gbar]
    (κ : G →+ Gbar) (x : Fin 4 → G → ℤ) (ρ : G) : Matrix (Fin 4 × Gbar) (Fin 4 × Gbar) ℤ :=
  core (fun q => cosetSum κ (x q)) (κ ρ)

/-- The bordered array

```
H = [ E   P̃ ]
    [ Q̃   C ]
```
-/
def border {G Gbar : Type*} [AddCommGroup G] [AddCommGroup Gbar] {s : ℕ} (κ : G →+ Gbar)
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G) :
    Matrix (Fin (4 * s) ⊕ (Fin 4 × G)) (Fin (4 * s) ⊕ (Fin 4 × G)) ℤ :=
  Matrix.fromBlocks E (rowStrip κ P) (colStrip κ Q) (core x ρ)

/-- **(H1)** `Q Qᵀ = I₄ ⊗ M` with `M` a `Gbar`-invariant table. -/
def H1 {Gbar : Type*} {s : ℕ} [AddCommGroup Gbar] (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (M : Gbar → ℤ) : Prop :=
  ∀ a b : Fin 4 × Gbar, (∑ c, Q a c * Q b c) = if a.1 = b.1 then M (a.2 - b.2) else 0

/-- **(H2)** `Σ PAF(t) = -M (κ t)` off the origin. -/
def H2 {G Gbar : Type*} [Fintype G] [AddCommGroup G] [AddCommGroup Gbar] (x : Fin 4 → G → ℤ)
    (κ : G →+ Gbar) (M : Gbar → ℤ) : Prop :=
  ∀ t : G, t ≠ 0 → sumPaf x t = -M (κ t)

/-- **(H3)** `E Eᵀ + w · P Pᵀ = N · I`. -/
def H3 {Gbar : Type*} {s : ℕ} [Fintype Gbar] [DecidableEq Gbar]
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ) (w N : ℤ) : Prop :=
  E * E.transpose + w • (P * P.transpose) = N • 1

/-- **(H4)** `E Qᵀ + P Ĉᵀ = 0`. -/
def H4 {Gbar : Type*} {s : ℕ} [Fintype Gbar] [DecidableEq Gbar]
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (Chat : Matrix (Fin 4 × Gbar) (Fin 4 × Gbar) ℤ) : Prop :=
  E * Q.transpose + P * Chat.transpose = 0

/-- The house Gram table `M = (4s+4)·I_i − 4·J_i` of `NOTE-B` §1.2, written as
a `Ḡ`-invariant function: `M(0) = 4s` — forced by the ansatz — and `M(ē) = −4`
for every nonzero class. -/
def houseM {Gbar : Type*} [Zero Gbar] [DecidableEq Gbar] (s : ℕ) : Gbar → ℤ :=
  fun e => if e = 0 then 4 * (s : ℤ) else -4

/-! ## The twist (`NOTE-B` §1.4) -/

/-- The diagonal `D̄ = diag(ψ̄(c))` acting on the border tables over the
quotient. -/
def twistDiagBar {Gbar : Type*} [DecidableEq Gbar] (ψbar : Gbar → ℤ) :
    Matrix (Fin 4 × Gbar) (Fin 4 × Gbar) ℤ :=
  Matrix.diagonal fun z : Fin 4 × Gbar => ψbar z.2

/-- The conjugator `S = diag(I_{4s}, I₄ ⊗ diag ψ)` of the `NOTE-B` §1.4
proposition. -/
def twistConj {G : Type*} [AddCommGroup G] [DecidableEq G] (s : ℕ) (ψ : AddChar G ℤ) :
    Matrix (Fin (4 * s) ⊕ (Fin 4 × G)) (Fin (4 * s) ⊕ (Fin 4 × G)) ℤ :=
  Matrix.fromBlocks 1 0 0 (Matrix.diagonal fun z : Fin 4 × G => ψ z.2)

/-! ## Theorem D data (`NOTE-B` §1.5) -/

/-- The Goethals--Seidel scalar table

```
          [  y0   y1   y2   y3 ]
Λ(y)  =   [ -y1   y0   y3  -y2 ]
          [ -y2  -y3   y0   y1 ]
          [ -y3   y2  -y1   y0 ]
```
-/
def Lam (y : Fin 4 → ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ y 0,  y 1,  y 2,  y 3;
     -y 1,  y 0,  y 3, -y 2;
     -y 2, -y 3,  y 0,  y 1;
     -y 3,  y 2, -y 1,  y 0]

/-- `ε = +1` when `κ ρ = 0` and `−1` otherwise (`NOTE-B` §1.5, setting
block). -/
def eps {G : Type*} [AddCommGroup G] (κ : G →+ ZMod 2) (ρ : G) : ℤ :=
  if κ ρ = 0 then 1 else -1

/-- `δ_q = σ_q(0) − σ_q(1)`, the twisted row sum. -/
def delta {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2) (x : G → ℤ) : ℤ :=
  cosetSum κ x 0 - cosetSum κ x 1

/-- `d = (δ₀, εδ₁, εδ₂, εδ₃)`, the vector the border equation of (D-d)
sees. -/
def dvec {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2) (x : Fin 4 → G → ℤ) (ρ : G) :
    Fin 4 → ℤ :=
  ![delta κ (x 0), eps κ ρ * delta κ (x 1), eps κ ρ * delta κ (x 2), eps κ ρ * delta κ (x 3)]

/-- The index-two character `ψ(g) = (−1)^{κ(g)}`, bundled as an
`AddChar G ℤ`. -/
def psi2 {G : Type*} [AddCommGroup G] (κ : G →+ ZMod 2) : AddChar G ℤ where
  toFun g := if κ g = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro a b
    have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hcases (κ a) with ha | ha <;> rcases hcases (κ b) with hb | hb <;>
      simp only [map_add, ha, hb] <;> decide

/-- Row sums of the seed quadruple. -/
def rvec {G : Type*} [Fintype G] (x : Fin 4 → G → ℤ) : Fin 4 → ℤ :=
  fun q => ∑ g, x q g

/-- The `ψ`-twist of a seed quadruple, `x ↦ (g ↦ (−1)^{κ g} x_q(g))`. -/
def seedTwist {G : Type*} [AddCommGroup G] (κ : G →+ ZMod 2) (x : Fin 4 → G → ℤ) :
    Fin 4 → G → ℤ :=
  fun q g => psi2 κ g * x q g

/-- The doubled row table `P[r][(J,c)] = (−1)^c · P₁[r][J]` (`NOTE-B` §1.5,
(D-e)). -/
def doubleRow (P : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ :=
  fun r z => if z.2 = 0 then P r z.1 else -P r z.1

/-- The doubled column table `Q[(I,0)] = Q₁[I]`, `Q[(I,1)] = −Q₁[I]`. -/
def doubleCol (Q : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin 4 × ZMod 2) (Fin (4 * 1)) ℤ :=
  fun z c => if z.2 = 0 then Q z.1 c else -Q z.1 c

/-! ## Theorem A (`NOTE-B` §1.1) -/

/-- **Theorem A, sufficiency** (`NOTE-B` §1.1).

Let `κ : G →+ Ḡ` be an additive hom all of whose fibers have size `w`, let
`ρ ∈ G`, and let the corner `E`, the border tables `P` and `Q` and the seed
quadruple `x` be sign valued.  If

* **(H1)** `Q Qᵀ = I₄ ⊗ M` for some `M : Ḡ → ℤ`, and
* **(H2)** `Σ PAF(t) = −M(κ t)` for every `t ≠ 0`, and
* **(H3)** `E Eᵀ + w · P Pᵀ = N · I`, and
* **(H4)** `E Qᵀ + P Ĉᵀ = 0`, with `Ĉ = GS(σ₀,…,σ₃; κρ)` the compressed core,

then the bordered array is a Hadamard matrix of order `N = 4(|G| + s)`.

Surjectivity of `κ` is **not** needed in this direction: only the constancy of
the fiber size enters. -/
theorem theoremA_sufficiency {G Gbar : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup Gbar] [Fintype Gbar] [DecidableEq Gbar] {s w : ℕ} (κ : G →+ Gbar)
    (hw : ∀ c : Gbar, (Finset.univ.filter fun g : G => κ g = c).card = w)
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G)
    (hE : ∀ r c, IsSign (E r c)) (hP : ∀ r z, IsSign (P r z))
    (hQ : ∀ z c, IsSign (Q z c)) (hx : ∀ q g, IsSign (x q g))
    (M : Gbar → ℤ) (h1 : H1 Q M) (h2 : H2 x κ M)
    (h3 : H3 E P (w : ℤ) (4 * ((Fintype.card G : ℤ) + s)))
    (h4 : H4 E P Q (chat κ x ρ)) :
    Matrix.IsHadamard (border κ E P Q x ρ) := by
  sorry

/-- **Theorem A** (`NOTE-B` §1.1), both directions.

For a **surjective** hom `κ` with all fibers of size `w` and sign-valued data,
the bordered array is a Hadamard matrix (necessarily of order
`N = 4(|G| + s)`) **if and only if** (H1)--(H4) hold.

`M` is automatically symmetric and satisfies `M 0 = 4s`, so the "`−4s` on
`K ∖ {0}`" tier of the profile is forced by the ansatz rather than chosen. -/
theorem theoremA {G Gbar : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup Gbar] [Fintype Gbar] [DecidableEq Gbar] {s w : ℕ} (κ : G →+ Gbar)
    (hκ : Function.Surjective κ)
    (hw : ∀ c : Gbar, (Finset.univ.filter fun g : G => κ g = c).card = w)
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G)
    (hE : ∀ r c, IsSign (E r c)) (hP : ∀ r z, IsSign (P r z))
    (hQ : ∀ z c, IsSign (Q z c)) (hx : ∀ q g, IsSign (x q g)) :
    Matrix.IsHadamard (border κ E P Q x ρ) ↔
      (∃ M : Gbar → ℤ, H1 Q M ∧ H2 x κ M)
        ∧ H3 E P (w : ℤ) (4 * ((Fintype.card G : ℤ) + s))
        ∧ H4 E P Q (chat κ x ρ) := by
  sorry

/-! ## Theorem B and its degenerations (`NOTE-B` §1.2--§1.3) -/

/-- **Theorem B** (`NOTE-B` §1.2).  For the house Gram table, hypothesis (H2)
of Theorem A is exactly the **two-tier PAF profile**

```
Σ_q PAF_q(t) = 4n·δ₀ − 4s·[t ∈ K∖{0}] + 4·[t ∉ K].
```

The sign condition on the seeds is used in one direction only: (H2) constrains
`t ≠ 0`, and the value `Σ PAF(0) = 4n` at the origin is supplied by
sign-valuedness alone. -/
theorem theoremB_profile {G Gbar : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    [AddCommGroup Gbar] [DecidableEq Gbar] (x : Fin 4 → G → ℤ) (hx : ∀ q g, IsSign (x q g))
    (κ : G →+ Gbar) (s : ℕ) :
    H2 x κ (houseM s) ↔
      ∀ t : G, sumPaf x t
        = 4 * (Fintype.card G : ℤ) * (if t = 0 then 1 else 0)
          - 4 * (s : ℤ) * (if t ≠ 0 ∧ κ t = 0 then 1 else 0)
          + 4 * (if κ t ≠ 0 then 1 else 0) := by
  sorry

/-- **The classical Goethals--Seidel theorem over an abelian group**
(`NOTE-B` §1.2, the `s = 0` degeneration; Wallis--Whiteman 1972, Theorem 11).

Four sign-valued sequences on a finite abelian group whose aggregate periodic
autocorrelation vanishes off the origin assemble, through the
Goethals--Seidel array, into a Hadamard matrix of order `4|G|` — for **every**
reflection shift `ρ`, not just the group inversion `ρ = 0`. -/
theorem goethalsSeidel_abelian {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    [Nonempty G] (x : Fin 4 → G → ℤ) (ρ : G) (hx : ∀ q g, IsSign (x q g))
    (hprofile : ∀ t : G, sumPaf x t = 4 * (Fintype.card G : ℤ) * (if t = 0 then 1 else 0)) :
    Matrix.IsHadamard (core x ρ) := by
  sorry

/-- **The Wallis--Whiteman / Spence bordered construction**
(`NOTE-B` §1.2, the `s = 1, i = 1` degeneration).

A four-by-four corner `E`, border tables `P` and `Q` with `Q Qᵀ = 4 · I₄`, and
four sign-valued sequences on a finite abelian group with the index-one
profile `Σ PAF(t) = −4` off the origin, satisfying (H3) and (H4), assemble
into a Hadamard matrix of order `4(|G| + 1)` — for every reflection shift
`ρ`. -/
theorem borderedGS_index_one {G Gbar : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup Gbar] [Fintype Gbar] [DecidableEq Gbar] [Subsingleton Gbar]
    (κ : G →+ Gbar)
    (E : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ)
    (P : Matrix (Fin (4 * 1)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * 1)) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G)
    (hE : ∀ r c, IsSign (E r c)) (hP : ∀ r z, IsSign (P r z))
    (hQ : ∀ z c, IsSign (Q z c)) (hx : ∀ q g, IsSign (x q g))
    (h1 : ∀ a b : Fin 4 × Gbar, (∑ c, Q a c * Q b c) = if a.1 = b.1 then 4 else 0)
    (h2 : ∀ t : G, t ≠ 0 → sumPaf x t = -4)
    (h3 : E * E.transpose + (Fintype.card G : ℤ) • (P * P.transpose)
      = (4 * ((Fintype.card G : ℤ) + 1)) • 1)
    (h4 : E * Q.transpose + P * (chat κ x ρ).transpose = 0) :
    Matrix.IsHadamard (border κ E P Q x ρ) := by
  sorry

/-- **D5** (`NOTE-B` §1.3).  Summing the house profile over the whole group
gives the second moment of the row sums:

```
Σ_q r_q² = 4n − 4s(w−1) + 4(n−w) = 8n − 4w(s+1) + 4s.
```

Only the fiber over `0` — i.e. `|K| = w` — enters, and the hypothesis says
exactly that: neither surjectivity of `κ`, nor the index, nor the size of any
other fiber is used. -/
theorem D5 {G Gbar : Type*} [Fintype G] [AddCommGroup G]
    [AddCommGroup Gbar] [DecidableEq Gbar] {s w : ℕ} (κ : G →+ Gbar)
    (hker : (Finset.univ.filter fun g : G => κ g = 0).card = w)
    (x : Fin 4 → G → ℤ) (hx : ∀ q g, IsSign (x q g)) (h2 : H2 x κ (houseM s)) :
    (∑ q, (∑ g, x q g) ^ 2)
      = 8 * (Fintype.card G : ℤ) - 4 * (w : ℤ) * ((s : ℤ) + 1) + 4 * (s : ℤ) := by
  sorry

/-- **D6** (`NOTE-B` §1.3).  At index one the whole group is the kernel, so
`D5` reads `Σ_q r_q² = 4(n − ns + s)`; non-negativity of a sum of squares
gives

```
n(s − 1) ≤ s.
```
-/
theorem D6 {G Gbar : Type*} [Fintype G] [AddCommGroup G]
    [AddCommGroup Gbar] [DecidableEq Gbar] [Subsingleton Gbar] {s : ℕ} (κ : G →+ Gbar)
    (x : Fin 4 → G → ℤ) (hx : ∀ q g, IsSign (x q g)) (h2 : H2 x κ (houseM s)) :
    (Fintype.card G : ℤ) * ((s : ℤ) - 1) ≤ (s : ℤ) := by
  sorry

/-! ## Lemma T and the twist (`NOTE-B` §1.4) -/

/-- **Lemma T** (`NOTE-B` §1.4).  For a character `ψ` with `ψ² = 1`,
`PAF_{ψ x}(t) = ψ(t) · PAF_x(t)`. -/
theorem lemmaT {G : Type*} [AddCommGroup G] [Fintype G] (ψ : AddChar G ℤ)
    (hsq : ∀ g : G, ψ g * ψ g = 1) (x : G → ℤ) (t : G) :
    paf (fun g => ψ g * x g) t = ψ t * paf x t := by
  sorry

/-- **The `s = 1` profile bijection** (`NOTE-B` §1.4).  A quadruple satisfies
the `i = 1` profile `Σ PAF(t) = -4` off the origin iff its `ψ`-twist satisfies
the `i = 2` profile: `-4` on `ker κ ∖ {0}` and `+4` off `ker κ`. -/
theorem twist_profile_iff {G : Type*} [AddCommGroup G] [Fintype G] (ψ : AddChar G ℤ)
    (hsq : ∀ g : G, ψ g * ψ g = 1) (κ : G →+ ZMod 2)
    (hψ : ∀ g : G, ψ g = if κ g = 0 then 1 else -1) (x : Fin 4 → G → ℤ) :
    (∀ t : G, t ≠ 0 → sumPaf x t = -4) ↔
      ∀ t : G, t ≠ 0 → sumPaf (fun q g => ψ g * x q g) t = if κ t = 0 then -4 else 4 := by
  sorry

/-- **A twist with `ψ(ρ) = 1` is a diagonal conjugation** (`NOTE-B` §1.4,
Proposition).  The twisted instance `x' = ψ x`, `P' = P D̄`, `Q' = D̄ Q`,
`E' = E` assembles to `S H S`. -/
theorem twist_isConjugation {G Gbar : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup Gbar] [Fintype Gbar] [DecidableEq Gbar] {s : ℕ}
    (κ : G →+ Gbar) (ψ : AddChar G ℤ) (hsq : ∀ g : G, ψ g * ψ g = 1)
    (ψbar : Gbar → ℤ) (hfac : ∀ g : G, ψ g = ψbar (κ g)) (ρ : G) (hρ : ψ ρ = 1)
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (x : Fin 4 → G → ℤ) :
    border κ E (P * twistDiagBar ψbar) (twistDiagBar ψbar * Q)
        (fun q g => ψ g * x q g) ρ =
      twistConj s ψ * border κ E P Q x ρ * twistConj s ψ := by
  sorry

/-- **The twist manufactures nothing new when `ψ(ρ) = 1`** (`NOTE-B` §1.4):
the twisted bordered array is Hadamard exactly when the original is. -/
theorem twist_isHadamard_iff {G Gbar : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup Gbar] [Fintype Gbar] [DecidableEq Gbar] {s : ℕ}
    (κ : G →+ Gbar) (ψ : AddChar G ℤ) (hsq : ∀ g : G, ψ g * ψ g = 1)
    (ψbar : Gbar → ℤ) (hfac : ∀ g : G, ψ g = ψbar (κ g)) (ρ : G) (hρ : ψ ρ = 1)
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (x : Fin 4 → G → ℤ) :
    Matrix.IsHadamard (border κ E (P * twistDiagBar ψbar)
        (twistDiagBar ψbar * Q) (fun q g => ψ g * x q g) ρ) ↔
      Matrix.IsHadamard (border κ E P Q x ρ) := by
  sorry

/-! ## Theorem D (`NOTE-B` §1.5) -/

/-- **`Σ_q δ_q² = 4`** (`NOTE-B` §1.5, (D-d)).  At index two the binding
character is `ℤ`-valued, so the note's Parseval step is a pure integer
identity: `Σ_q δ_q²` is the total mass of the `ψ`-twisted profile, and the
house profile at `s = 1` evaluates it to `4n − 4(w−1) − 4(n−w) = 4`. -/
theorem deltaSqSum_eq_four {G : Type*} [Fintype G] [AddCommGroup G]
    (κ : G →+ ZMod 2) (x : Fin 4 → G → ℤ) (hx : ∀ q g, IsSign (x q g))
    (h2 : H2 x κ (houseM 1)) :
    (∑ q, delta κ (x q) ^ 2) = 4 := by
  sorry

/-- **Theorem D, clauses (D-a) and (D-b)** (`NOTE-B` §1.5).

At `(s, i) = (1, 2)` the Gram table is forced: `M(0) = 4` by the ansatz and
`M(1) = ±4`.  In the genuine branch `M(1) = −4` the column table pair-negates,
`Q[(I,1)] = −Q[(I,0)]`, and the reduced table `U[I] = Q[(I,0)]` is a `4×4`
Hadamard matrix. -/
theorem theoremD_tables (Q : Matrix (Fin 4 × ZMod 2) (Fin 4) ℤ) (hQ : ∀ z c, IsSign (Q z c))
    (M : ZMod 2 → ℤ) (h1 : H1 (s := 1) Q M) :
    M 0 = 4 ∧ (M 1 = 4 ∨ M 1 = -4) ∧
      (M 1 = -4 →
        (∀ I : Fin 4, Q (I, 1) = -Q (I, 0)) ∧
          Matrix.IsHadamard (Matrix.of fun I c : Fin 4 => Q (I, 0) c)) := by
  sorry

/-- **Theorem D, clause (D-c)** (`NOTE-B` §1.5).

Once the column table has pair-negated, (H4) forces the row table to
pair-negate too: summing the two rows of a block of `Ĉ` gives `Λ(r)`, `D5`
gives `Σ_q r_q² = N ≠ 0` so `Λ(r)` is nonsingular, and the column sums
`P[r][2J] + P[r][2J+1]` are annihilated.  The doubling then turns (H3) into
`E Eᵀ + 2w·p pᵀ = N·I₄`, and the integer forcing splits it: `p` is a `4×4`
Hadamard matrix and so is `E`.

This is sharper than `D3`, which needs `w > 2s`: the doubling turned `w` into
`2w`, so `w ≥ 2` suffices. -/
theorem theoremD_rowTable {G : Type*} [Fintype G] [AddCommGroup G] {w : ℕ}
    (κ : G →+ ZMod 2)
    (hw : ∀ c : ZMod 2, (Finset.univ.filter fun g : G => κ g = c).card = w) (hw2 : 2 ≤ w)
    (E : Matrix (Fin 4) (Fin 4) ℤ) (P : Matrix (Fin 4) (Fin 4 × ZMod 2) ℤ)
    (Q : Matrix (Fin 4 × ZMod 2) (Fin 4) ℤ) (x : Fin 4 → G → ℤ) (ρ : G)
    (hE : ∀ r c, IsSign (E r c)) (hP : ∀ r z, IsSign (P r z)) (hx : ∀ q g, IsSign (x q g))
    (h2 : H2 x κ (houseM 1))
    (h3 : H3 (s := 1) E P (w : ℤ) (4 * ((Fintype.card G : ℤ) + 1)))
    (h4 : H4 (s := 1) E P Q (chat κ x ρ))
    (hQpair : ∀ I : Fin 4, Q (I, 1) = -Q (I, 0)) :
    (∀ r J : Fin 4, P r (J, 1) = -P r (J, 0)) ∧
      Matrix.IsHadamard (Matrix.of fun r J : Fin 4 => P r (J, 0)) ∧
      Matrix.IsHadamard E := by
  sorry

/-- **Theorem D, clause (D-d)** (`NOTE-B` §1.5).

With the two tables pair-negated and `U` Hadamard, (H4) — a `4 × 8` condition
— collapses to the single `4 × 4` equation

```
E Uᵀ + p Λ(d)ᵀ = 0,   equivalently   4·E = −p·Λ(d)ᵀ·U.
```

The `4 •` form keeps everything in `ℤ` where the note writes
`E = −¼·p·Λ(d)ᵀ·U`. -/
theorem theoremD_border {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (x : Fin 4 → G → ℤ) (ρ : G)
    (E : Matrix (Fin 4) (Fin 4) ℤ) (P : Matrix (Fin 4) (Fin 4 × ZMod 2) ℤ)
    (Q : Matrix (Fin 4 × ZMod 2) (Fin 4) ℤ)
    (hQpair : ∀ I : Fin 4, Q (I, 1) = -Q (I, 0))
    (hPpair : ∀ r J : Fin 4, P r (J, 1) = -P r (J, 0))
    (hU : Matrix.IsHadamard (Matrix.of fun I c : Fin 4 => Q (I, 0) c)) :
    H4 (s := 1) E P Q (chat κ x ρ) ↔
      (4 : ℤ) • E = -((Matrix.of fun r J : Fin 4 => P r (J, 0))
        * (Lam (dvec κ x ρ)).transpose * (Matrix.of fun I c : Fin 4 => Q (I, 0) c)) := by
  sorry

/-- **Theorem D, the transport clause of (D-e)** (`NOTE-B` §1.5).

An `s = 1, i = 1` bordered instance `(E₁, P₁, Q₁)` for a sign-valued quadruple
`x` with the index-one profile `Σ PAF(t) = −4` off the origin transports
across the doubling: the doubled tables `doubleRow P₁`, `doubleCol Q₁`, the
same corner `E₁`, and the **twisted** seeds `ψ x` form a valid `s = 1, i = 2`
bordered instance for `κ : G →+ ZMod 2`.

`hd` is the note's `d = r`, and it is not decoration: the transported system
reads `P₁ Λ(d)ᵀ = P₁ Λ(r)ᵀ`, so with `Λ` injective and `P₁` invertible it
holds precisely when `d = r`.  It is automatic in the `ε = +1` branch. -/
theorem theoremD_transport {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G] {w : ℕ}
    (κ : G →+ ZMod 2)
    (hw : ∀ c : ZMod 2, (Finset.univ.filter fun g : G => κ g = c).card = w)
    (E₁ : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ) (P₁ Q₁ : Matrix (Fin 4) (Fin 4) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G)
    (hE : ∀ r c, IsSign (E₁ r c)) (hP : ∀ r J, IsSign (P₁ r J)) (hQ : ∀ I c, IsSign (Q₁ I c))
    (hx : ∀ q g, IsSign (x q g))
    (hQgram : Q₁ * Q₁.transpose = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hprofile : ∀ t : G, t ≠ 0 → sumPaf x t = -4)
    (h3 : E₁ * E₁.transpose + (Fintype.card G : ℤ) • (P₁ * P₁.transpose)
      = (4 * ((Fintype.card G : ℤ) + 1)) • 1)
    (h4 : E₁ * Q₁.transpose + P₁ * (Lam (rvec x)).transpose = 0)
    (hd : dvec κ (seedTwist κ x) ρ = rvec x) :
    Matrix.IsHadamard (border κ E₁ (doubleRow P₁) (doubleCol Q₁) (seedTwist κ x) ρ) := by
  sorry

/-! ## The index-two collapse (`NOTE-B` §1.6) -/

/-- **The index-two collapse, seed-problem bijection** (`NOTE-B` §1.6,
Corollary — the seed-problem bijection clause; the characteristic-subgroup
and automorphism-equivariance clauses are not formalized).

The character twist `x ↦ ψ x` with `ψ(g) = (−1)^{κ g}` is

1. an **involution** of quadruples,
2. a bijection of **sign-valued** quadruples, and
3. a bijection from the `s = 1, i = 1` seed problem — the profile
   `Σ PAF(t) = −4` for `t ≠ 0` — onto the `s = 1, i = 2` seed problem,
   hypothesis (H2) of Theorem A for the house Gram table `houseM 1`.

So the two seed problems are one problem.  The bijection is of **seed
problems, not of matrices**: it does not say the assembled Hadamard matrices
are equivalent (`NOTE-B` §3.4 proves they are not, at order 668). -/
theorem collapse_seedProblem_bijection {G : Type*} [AddCommGroup G] [Fintype G]
    (κ : G →+ ZMod 2) (x : Fin 4 → G → ℤ) :
    seedTwist κ (seedTwist κ x) = x ∧
      ((∀ q g, IsSign (x q g)) ↔ ∀ q g, IsSign (seedTwist κ x q g)) ∧
      ((∀ t : G, t ≠ 0 → sumPaf x t = -4) ↔ H2 (seedTwist κ x) κ (houseM 1)) := by
  sorry

/-! ## The `H(52)` gate record (`NOTE-B` §2.2, cert 03)

A from-scratch `s = 1, i = 2` instance on the **non-cyclic** group
`G = ZMod 2 × ZMod 2 × ZMod 3` with `w = 6`, in the `ε = +1` branch
(`κ ρ = 0`) — the Theorem-D instance the four decoded `i = 2` records do not
exercise.  The literals are those of `Hadamard-B/data/h52-gate.json`. -/

/-- The gate group `G = ZMod 2 × ZMod 2 × ZMod 3`, of order 12. -/
abbrev G52 : Type := ZMod 2 × ZMod 2 × ZMod 3

/-- The flat index of a group element, in the row-major mixed-radix order of
`Hadamard-B/tools/bordered_gs.py`: `(a,b,c) ↦ 6a + 3b + c`. -/
def gidx52 (z : G52) : Fin 12 :=
  ⟨6 * z.1.val + 3 * z.2.1.val + z.2.2.val, by
    have h0 : z.1.val < 2 := ZMod.val_lt z.1
    have h1 : z.2.1.val < 2 := ZMod.val_lt z.2.1
    have h2 : z.2.2.val < 3 := ZMod.val_lt z.2.2
    omega⟩

/-- The flat index of a border-table column `(J, b)`, class index fastest:
`(J, b) ↦ 2J + b`. -/
def pairIdx (z : Fin 4 × ZMod 2) : Fin 8 :=
  ⟨2 * z.1.val + z.2.val, by
    have h0 : z.1.val < 4 := z.1.isLt
    have h1 : z.2.val < 2 := ZMod.val_lt z.2
    omega⟩

/-- The index-two character of `G`, `coset_divisors = [2,1,1]`: the first
coordinate. -/
def kappa52 : G52 →+ ZMod 2 where
  toFun z := z.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The reflection shift `ρ`, the record's `r_shift = (0,0,0)`.  Since
`κ ρ = 0` this instance is the `ε = +1` branch. -/
def rho52 : G52 := 0

/-- The seed literals of the gate record. -/
def seed52Data : Vector (Vector Int 12) 4 :=
  #v[
    #v[
      -1, -1, 1, 1, 1, -1, -1, 1, -1, 1, -1, -1
    ],
    #v[
      -1, -1, 1, -1, -1, 1, 1, 1, -1, -1, -1, -1
    ],
    #v[
      1, -1, -1, 1, -1, -1, 1, 1, -1, -1, -1, -1
    ],
    #v[
      -1, 1, -1, 1, -1, -1, 1, 1, -1, -1, -1, -1
    ]
  ]

/-- The four seed sequences of the gate record, as functions on `G`. -/
def seed52 : Fin 4 → G52 → ℤ := fun q g => (seed52Data.get q).get (gidx52 g)

/-- The corner literals of the gate record. -/
def corner52Data : Vector (Vector Int 4) 4 :=
  #v[
    #v[
      -1, -1, -1, 1
    ],
    #v[
      -1, -1, 1, -1
    ],
    #v[
      -1, 1, -1, -1
    ],
    #v[
      1, -1, -1, -1
    ]
  ]

/-- The corner `E` of the gate record. -/
def E52 : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ :=
  fun r c => (corner52Data.get r).get c

/-- The row-table literals of the gate record. -/
def rowTable52Data : Vector (Vector Int 8) 4 :=
  #v[
    #v[
      -1, 1, 1, -1, 1, -1, -1, 1
    ],
    #v[
      1, -1, -1, 1, 1, -1, -1, 1
    ],
    #v[
      1, -1, 1, -1, -1, 1, -1, 1
    ],
    #v[
      -1, 1, -1, 1, -1, 1, -1, 1
    ]
  ]

/-- The row table `P` of the gate record, indexed by `Fin 4 × ZMod 2`. -/
def P52 : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ :=
  fun r z => (rowTable52Data.get r).get (pairIdx z)

/-- The column-table literals of the gate record. -/
def colTable52Data : Vector (Vector Int 8) 4 :=
  #v[
    #v[
      1, -1, 1, -1, 1, -1, -1, 1
    ],
    #v[
      -1, 1, -1, 1, 1, -1, -1, 1
    ],
    #v[
      -1, 1, 1, -1, -1, 1, -1, 1
    ],
    #v[
      1, -1, -1, 1, -1, 1, -1, 1
    ]
  ]

/-- The column table `Q` of the gate record.  The record stores it transposed:
`Q[(I,b)][r] = col_table[r][2I + b]`. -/
def Q52 : Matrix (Fin 4 × ZMod 2) (Fin (4 * 1)) ℤ :=
  fun z c => (colTable52Data.get c).get (pairIdx z)

/-! ## The order-20 boundary record (`NOTE-B` §2.2, cert 05)

The `w = 2s` hypothesis boundary, on `G = ZMod 2 × ZMod 2` with `K` the
**diagonal** subgroup — an arbitrary index-two subgroup rather than a
coordinate kernel, which the surjective-hom model handles as `κ(a,b) = a + b`.
The companion instance T2 of that record declares the transpose-negated
orientation and is out of scope by construction. -/

/-- The boundary group `G = ZMod 2 × ZMod 2`, of order 4. -/
abbrev G20 : Type := ZMod 2 × ZMod 2

/-- The flat index of a group element, row-major mixed radix:
`(a,b) ↦ 2a + b`. -/
def gidx20 (z : G20) : Fin 4 :=
  ⟨2 * z.1.val + z.2.val, by
    have h0 : z.1.val < 2 := ZMod.val_lt z.1
    have h1 : z.2.val < 2 := ZMod.val_lt z.2
    omega⟩

/-- The **diagonal** index-two subgroup `K = ⟨(1,1)⟩`, presented as the
surjective hom `κ(a,b) = a + b`. -/
def kappa20 : G20 →+ ZMod 2 where
  toFun z := z.1 + z.2
  map_zero' := rfl
  map_add' a b := add_add_add_comm a.1 b.1 a.2 b.2

/-- The reflection shift `ρ = (1,1)` of the boundary record.  Note
`κ ρ = 0`. -/
def rho20 : G20 := (1, 1)

/-- The seed literals of the boundary record. -/
def seed20Data : Vector (Vector Int 4) 4 :=
  #v[
    #v[
      -1, -1, 1, 1
    ],
    #v[
      -1, 1, -1, 1
    ],
    #v[
      1, -1, -1, -1
    ],
    #v[
      -1, -1, -1, -1
    ]
  ]

/-- The four seed sequences of the boundary record. -/
def seed20 : Fin 4 → G20 → ℤ := fun q g => (seed20Data.get q).get (gidx20 g)

/-- The corner literals of the boundary record. -/
def corner20Data : Vector (Vector Int 4) 4 :=
  #v[
    #v[
      -1, -1, -1, -1
    ],
    #v[
      1, 1, -1, -1
    ],
    #v[
      1, -1, 1, -1
    ],
    #v[
      -1, 1, 1, -1
    ]
  ]

/-- The corner `E` of the boundary record. -/
def E20 : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ :=
  fun r c => (corner20Data.get r).get c

/-- The row-table literals of the boundary record. -/
def rowTable20Data : Vector (Vector Int 8) 4 :=
  #v[
    #v[
      -1, 1, 1, -1, -1, 1, 1, -1
    ],
    #v[
      1, -1, 1, -1, -1, 1, -1, 1
    ],
    #v[
      1, -1, -1, 1, -1, 1, 1, -1
    ],
    #v[
      1, -1, 1, -1, 1, -1, 1, -1
    ]
  ]

/-- The row table `P` of the boundary record. -/
def P20 : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ :=
  fun r z => (rowTable20Data.get r).get (pairIdx z)

/-- The column-table literals of the boundary record. -/
def colRows20Data : Vector (Vector Int 4) 8 :=
  #v[
    #v[
      1, -1, -1, -1
    ],
    #v[
      -1, 1, 1, 1
    ],
    #v[
      -1, -1, 1, -1
    ],
    #v[
      1, 1, -1, 1
    ],
    #v[
      1, 1, 1, -1
    ],
    #v[
      -1, -1, -1, 1
    ],
    #v[
      1, -1, 1, 1
    ],
    #v[
      -1, 1, -1, -1
    ]
  ]

/-- The column table `Q` of the boundary record.  This record stores `Q` row by
row — `Q[(I,b)][r] = col_rows[2I + b][r]` — not transposed. -/
def Q20 : Matrix (Fin 4 × ZMod 2) (Fin (4 * 1)) ℤ :=
  fun z c => (colRows20Data.get (pairIdx z)).get c

/-! ## The two instances, through the theorem (`NOTE-B` §2.2) -/

/-- **The `H(52)` gate instance.**  The bordered Goethals--Seidel array of the
gate record is a Hadamard matrix of order `4(12+1) = 52`.

Everything used is a hypothesis of Theorem A on a group of order `12`; the
Hadamard property itself is deduced, never computed — the assembled `52 × 52`
matrix and its `52³` product are never formed. -/
theorem hadamard_52_bordered :
    Matrix.IsHadamard (border kappa52 E52 P52 Q52 seed52 rho52) := by
  sorry

/-- The gate instance realises the genuine branch of Theorem D: the Gram table
has `M(1) = −4`, so the column table pair-negates onto a `4 × 4` Hadamard
matrix `U`.  This is `theoremD_tables` read on the gate record — the formal
counterpart of cert 03's check of clauses (D-a)/(D-b). -/
theorem gate52_columnTable :
    (∀ I : Fin 4, Q52 (I, 1) = -Q52 (I, 0)) ∧
      Matrix.IsHadamard (Matrix.of fun I c : Fin 4 => Q52 (I, 0) c) := by
  sorry

/-- **A Hadamard matrix of order 52 exists**, as a `Matrix (Fin 52) (Fin 52) ℤ`.

The order is long settled and no novelty is claimed; the *route* is the point.
The existence statement is obtained from Theorem A applied to twelve-element
data, with no `52 × 52` product anywhere in the trust base. -/
theorem hadamardExists_52 : HadamardExists 52 := by
  sorry

/-- **The order-20 boundary instance T1.**  The bordered array of the boundary
record is a Hadamard matrix of order `4(4+1) = 20`.

Theorem A does not care that `w = 2s`, nor that `K` is the diagonal rather
than a coordinate kernel — that is the payoff of modelling the quotient as a
surjective hom. -/
theorem hadamard_20_bordered :
    Matrix.IsHadamard (border kappa20 E20 P20 Q20 seed20 rho20) := by
  sorry

/-- **A Hadamard matrix of order 20 exists**, from the boundary record. -/
theorem hadamardExists_20 : HadamardExists 20 := by
  sorry

end HadamardBFormal
