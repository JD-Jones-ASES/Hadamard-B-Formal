/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import HadamardBFormal.Compression

/-!
# The house form and its two classical degenerations

`NOTE-B` §1.2 records two degenerations of the house profile which are classical
theorems, and this file proves both.

* `goethalsSeidel_abelian` (`s = 0`, `K = G`, `i = 1`): the profile is
  `Σ PAF(t) = 4n·δ₀`, the border is empty, and the core alone is Hadamard.  This
  is the **classical Goethals--Seidel theorem over an abelian group**
  (Wallis--Whiteman 1972, Theorem 11).  It strictly generalizes
  `Hadamard-formal`'s `goethalsSeidel_isHadamard`, which is fixed at the group
  inversion `ρ = 0`: here the reflection shift is arbitrary.
* `borderedGS_index_one` (`s = 1`, `i = 1`): the profile is `Σ PAF(t) = −4` off
  the origin, and the bordered array is Hadamard.  This is the
  **Wallis--Whiteman / Spence bordered construction**.  It is the `s = 1` case of
  `borderedGS_subsingleton`, which carries an arbitrary corner size.

At `i = 1` the compression lemma (`NOTE-B` §1.1, Lemma 3) collapses: every
`K`-coset is all of `G`, so `Σ_h x(h − g)` is just the row sum of `x` and no
fiber reindexing is needed.  That collapse is `compression_index_one`, proved
here from the block-level `gsBlock_sum_eq` — a direct argument, independent of
the general Lemma 3 in `Compression.lean`.

`borderedGS_subsingleton` is now a corollary of `theoremA_sufficiency`
(`Compression.lean`): a trivial quotient has one fiber, of size `|G|`, and the
Gram table `M` is the constant `4s`.
-/

namespace HadamardBFormal

open scoped BigOperators Matrix

/-! ### The core alone: the classical Goethals--Seidel theorem -/

/-- Under the `s = 0` profile the core has Gram `4n · I`. -/
theorem core_mul_transpose {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (x : Fin 4 → G → ℤ) (ρ : G)
    (hprofile : ∀ t : G, sumPaf x t = 4 * (Fintype.card G : ℤ) * (if t = 0 then 1 else 0)) :
    core x ρ * (core x ρ).transpose =
      (Fintype.card (Fin 4 × G) : ℤ) • (1 : Matrix (Fin 4 × G) (Fin 4 × G) ℤ) := by
  have hcard : (Fintype.card (Fin 4 × G) : ℤ) = 4 * (Fintype.card G : ℤ) := by
    rw [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  ext z z'
  obtain ⟨a, g⟩ := z
  obtain ⟨b, h⟩ := z'
  rw [core_gram, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, hcard]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, hprofile]
    congr 1
    simp [sub_eq_zero]
  · rw [if_neg hab, if_neg (by simp [hab])]
    ring

/-- **The classical Goethals--Seidel theorem over an abelian group**
(`NOTE-B` §1.2, the `s = 0` degeneration; Wallis--Whiteman 1972, Theorem 11).

Four sign-valued sequences on a finite abelian group whose aggregate periodic
autocorrelation vanishes off the origin assemble, through the Goethals--Seidel
array, into a Hadamard matrix of order `4|G|` — for **every** reflection shift
`ρ`, not just the group inversion `ρ = 0`. -/
theorem goethalsSeidel_abelian {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    [Nonempty G] (x : Fin 4 → G → ℤ) (ρ : G) (hx : ∀ q g, IsSign (x q g))
    (hprofile : ∀ t : G, sumPaf x t = 4 * (Fintype.card G : ℤ) * (if t = 0 then 1 else 0)) :
    Matrix.IsHadamard (core x ρ) := by
  refine Matrix.IsHadamard.of_mul_conjTranspose
    (fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (core_isSign x ρ hx i j)) ?_ ?_
  · rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact core_mul_transpose x ρ hprofile
  · rw [isRegular_iff_ne_zero]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Fin 4 × G) ≠ 0)

/-! ### The compression lemma at index one

At `i = 1` every fiber of `κ` is all of `G`, so a coset sum is a row sum and the
compressed core is the constant Goethals--Seidel array of the row sums. -/

/-- A coset sum over a trivial quotient is the row sum. -/
theorem cosetSum_subsingleton {G Gbar : Type*} [Fintype G] [DecidableEq Gbar]
    [Subsingleton Gbar] (κ : G → Gbar) (x : G → ℤ) (c : Gbar) :
    cosetSum κ x c = ∑ g, x g := by
  rw [cosetSum, Finset.filter_true_of_mem fun g _ => Subsingleton.elim (κ g) c]

/-- Row sums of a developed matrix do not see the row. -/
theorem dev_sum_row {G : Type*} [Fintype G] [AddCommGroup G] (x : G → ℤ) (g : G) :
    (∑ h, dev x g h) = ∑ k, x k := by
  calc (∑ h, dev x g h) = ∑ k, dev x g (Equiv.addRight g k) :=
        (Equiv.sum_comp (Equiv.addRight g) fun h => dev x g h).symm
    _ = ∑ k, x k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        change x (k + g - g) = x k
        congr 1
        abel

/-- Column sums of a developed matrix do not see the column. -/
theorem dev_sum_col {G : Type*} [Fintype G] [AddCommGroup G] (x : G → ℤ) (g : G) :
    (∑ h, dev x h g) = ∑ k, x k := by
  calc (∑ h, dev x h g) = ∑ k, dev x (reflect g k) g :=
        (Equiv.sum_comp (reflect g) fun h => dev x h g).symm
    _ = ∑ k, x k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [dev_apply, reflect_apply]
        congr 1
        abel

/-- **The block-level collapse.**  If every block of one Goethals--Seidel table
has constant row and column sums `v q`, and every block of a second table is
constantly `v q`, then summing a block of the first over a whole row reproduces
the corresponding entry of the second — signs included.

This is the sixteen-case bookkeeping behind `compression_index_one`; it is stated
for two unrelated index types because the two arrays live over `G` and over the
quotient. -/
theorem gsBlock_sum_eq {G Gb : Type*} [Fintype G] (r : Equiv.Perm G)
    (X : Fin 4 → Matrix G G ℤ) (v : Fin 4 → ℤ)
    (hrow : ∀ q g, (∑ h, X q g h) = v q) (hcol : ∀ q g, (∑ h, X q h g) = v q)
    (r' : Equiv.Perm Gb) (Y : Fin 4 → Matrix Gb Gb ℤ) (hY : ∀ q a b, Y q a b = v q)
    (I J : Fin 4) (g : G) (a b : Gb) :
    (∑ h, gsBlock r X I J g h) = gsBlock r' Y I J a b := by
  have hrow' : ∀ q g, (∑ h, X q g (r h)) = v q := fun q g =>
    (Equiv.sum_comp r fun h => X q g h).trans (hrow q g)
  have hcol' : ∀ q g, (∑ h, X q (r h) g) = v q := fun q g =>
    (Equiv.sum_comp r fun h => X q h g).trans (hcol q g)
  fin_cases I <;> fin_cases J <;>
    simp only [gsBlock, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.neg_apply, revCols_apply, Matrix.transpose_apply,
      Finset.sum_neg_distrib, hrow, hrow', hcol', hY]

/-- **Lemma 3 at index one** (`NOTE-B` §1.1).  When the quotient is trivial the
compression lemma collapses to the statement that summing a row of the core over
all of `G` reproduces the corresponding entry of the compressed core: no fiber
reindexing is involved, only `Σ_h x(h − g) = Σ_k x(k)`. -/
theorem compression_index_one {G Gbar : Type*} [Fintype G] [AddCommGroup G]
    [AddCommGroup Gbar] [DecidableEq Gbar] [Subsingleton Gbar] (κ : G →+ Gbar)
    (x : Fin 4 → G → ℤ) (ρ : G) (I J : Fin 4) (g : G) (c : Gbar) :
    (∑ h, core x ρ (I, g) (J, h)) = chat κ x ρ (I, κ g) (J, c) :=
  gsBlock_sum_eq (reflect ρ) (fun q => dev (x q)) (fun q => ∑ k, x q k)
    (fun q g => dev_sum_row (x q) g) (fun q g => dev_sum_col (x q) g)
    (reflect (κ ρ)) (fun q => dev (cosetSum κ (x q)))
    (fun q a b => cosetSum_subsingleton κ (x q) (b - a)) I J g (κ g) c

/-! ### The bordered construction at index one -/

/-- **Theorem A, sufficiency, at index one.**  With a trivial quotient the fiber
size is `w = |G|`, the Gram table `M` is forced to the constant `4s`, and the
hypotheses (H1)--(H4) suffice: the bordered array is Hadamard of order
`4(|G| + s)`.

At `s = 1` this is the Wallis--Whiteman / Spence bordered construction; see
`borderedGS_index_one`. -/
theorem borderedGS_subsingleton {G Gbar : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup Gbar] [Fintype Gbar] [DecidableEq Gbar] [Subsingleton Gbar] {s : ℕ}
    (κ : G →+ Gbar)
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G)
    (hE : ∀ r c, IsSign (E r c)) (hP : ∀ r z, IsSign (P r z))
    (hQ : ∀ z c, IsSign (Q z c)) (hx : ∀ q g, IsSign (x q g))
    (h1 : H1 Q fun _ => 4 * (s : ℤ))
    (h2 : H2 x κ fun _ => 4 * (s : ℤ))
    (h3 : H3 E P (Fintype.card G : ℤ) (4 * ((Fintype.card G : ℤ) + s)))
    (h4 : H4 E P Q (chat κ x ρ)) :
    Matrix.IsHadamard (border κ E P Q x ρ) := by
  have hw : ∀ c : Gbar, (Finset.univ.filter fun g : G => κ g = c).card = Fintype.card G := by
    intro c
    rw [Finset.filter_true_of_mem fun g _ => Subsingleton.elim (κ g) c, Finset.card_univ]
  exact theoremA_sufficiency κ hw E P Q x ρ hE hP hQ hx (fun _ => 4 * (s : ℤ)) h1 h2 h3 h4

/-- **The Wallis--Whiteman / Spence bordered construction**
(`NOTE-B` §1.2, the `s = 1, i = 1` degeneration).

A four-by-four corner `E`, border tables `P` and `Q` with `Q Qᵀ = 4 · I₄`, and
four sign-valued sequences on a finite abelian group with the index-one profile
`Σ PAF(t) = −4` off the origin, satisfying (H3) and (H4), assemble into a
Hadamard matrix of order `4(|G| + 1)` — for every reflection shift `ρ`. -/
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
  refine borderedGS_subsingleton κ E P Q x ρ hE hP hQ hx (fun a b => ?_) (fun t ht => ?_)
    ?_ h4
  · simpa using h1 a b
  · simpa using h2 t ht
  · simpa [H3] using h3

end HadamardBFormal
