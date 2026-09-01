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

The file also carries the **house form itself** (`NOTE-B` §1.2) and the two rows
of `NOTE-B` §1.3 that are one summation away from it:

* `houseM` — the table `M = (4s+4)·I_i − 4·J_i`, written as a `Ḡ`-invariant
  function `ē ↦ if ē = 0 then 4s else −4`;
* `theoremB_profile` — **Theorem B**: (H2) for the house table is exactly the
  two-tier PAF profile `4n·δ₀ − 4s·[t ∈ K∖0] + 4·[t ∉ K]`;
* `D5` — `Σ_q r_q² = 8n − 4w(s+1) + 4s`, obtained by summing the profile over
  `G` (the `t = 0` term is `4n` by the sign condition alone);
* `D6` — at index one, non-negativity of `D5` gives `n(s−1) ≤ s`.

`D5` and `D6` are the only rows of Theorem C in formal scope; `D1`--`D4` and the
classification corollary are deliberately out of scope (they need positive
semidefiniteness, rank over `ℝ`, and character orthogonality over `ℂ`).
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

/-! ### The house Gram table -/

/-- The house Gram table `M = (4s+4)·I_i − 4·J_i` of `NOTE-B` §1.2, written as a
`Ḡ`-invariant function: `M(0) = 4s` — forced by the ansatz, see `M_zero_of_H1` —
and `M(ē) = −4` for every nonzero class. -/
def houseM {Gbar : Type*} [Zero Gbar] [DecidableEq Gbar] (s : ℕ) : Gbar → ℤ :=
  fun e => if e = 0 then 4 * (s : ℤ) else -4

@[simp]
theorem houseM_zero {Gbar : Type*} [Zero Gbar] [DecidableEq Gbar] (s : ℕ) :
    houseM (Gbar := Gbar) s 0 = 4 * (s : ℤ) :=
  if_pos rfl

theorem houseM_of_ne {Gbar : Type*} [Zero Gbar] [DecidableEq Gbar] (s : ℕ) {e : Gbar}
    (he : e ≠ 0) : houseM s e = -4 :=
  if_neg he

/-! ### Theorem B -/

/-- **Theorem B** (`NOTE-B` §1.2).  For the house Gram table, hypothesis (H2) of
Theorem A is exactly the **two-tier PAF profile**

```
Σ_q PAF_q(t) = 4n·δ₀ − 4s·[t ∈ K∖{0}] + 4·[t ∉ K].
```

The sign condition on the seeds is used in one direction only: (H2) constrains
`t ≠ 0`, and the value `Σ PAF(0) = 4n` of the displayed profile at the origin is
supplied by `sumPaf_zero`, i.e. by sign-valuedness alone. -/
theorem theoremB_profile {G Gbar : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    [AddCommGroup Gbar] [DecidableEq Gbar] (x : Fin 4 → G → ℤ) (hx : ∀ q g, IsSign (x q g))
    (κ : G →+ Gbar) (s : ℕ) :
    H2 x κ (houseM s) ↔
      ∀ t : G, sumPaf x t
        = 4 * (Fintype.card G : ℤ) * (if t = 0 then 1 else 0)
          - 4 * (s : ℤ) * (if t ≠ 0 ∧ κ t = 0 then 1 else 0)
          + 4 * (if κ t ≠ 0 then 1 else 0) := by
  have hRHS : ∀ t : G,
      4 * (Fintype.card G : ℤ) * (if t = 0 then 1 else 0)
        - 4 * (s : ℤ) * (if t ≠ 0 ∧ κ t = 0 then 1 else 0)
        + 4 * (if κ t ≠ 0 then 1 else 0)
      = if t = 0 then 4 * (Fintype.card G : ℤ) else -houseM s (κ t) := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp
    · by_cases hkt : κ t = 0
      · rw [hkt, houseM_zero]
        simp [ht]
      · rw [houseM_of_ne s hkt]
        simp [ht, hkt]
  constructor
  · intro h2 t
    rw [hRHS t]
    by_cases ht : t = 0
    · subst ht
      rw [if_pos rfl]
      exact sumPaf_zero hx
    · rw [if_neg ht]
      exact h2 t ht
  · intro hprof t ht
    have h := hprof t
    rw [hRHS t, if_neg ht] at h
    exact h

/-! ### D5 and D6 -/

/-- The total mass of a periodic autocorrelation is the square of the row sum:
`Σ_t PAF_x(t) = (Σ_g x g)²`. -/
theorem sum_paf_eq_sq {G : Type*} [Fintype G] [AddCommGroup G] (x : G → ℤ) :
    (∑ t, paf x t) = (∑ g, x g) ^ 2 := by
  have hstep : ∀ u : G, (∑ t : G, x (u + t)) = ∑ k : G, x k := fun u =>
    Fintype.sum_equiv (Equiv.addLeft u) (fun t => x (u + t)) x fun _ => rfl
  calc (∑ t, paf x t) = ∑ t : G, ∑ u : G, x u * x (u + t) := rfl
    _ = ∑ u : G, ∑ t : G, x u * x (u + t) := Finset.sum_comm
    _ = ∑ u : G, x u * ∑ t : G, x (u + t) :=
        Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ u : G, x u * ∑ k : G, x k :=
        Finset.sum_congr rfl fun u _ => by rw [hstep u]
    _ = (∑ g, x g) ^ 2 := by rw [← Finset.sum_mul, sq]

/-- The total mass of the aggregate profile is the second moment of the row sums:
`Σ_t Σ PAF(t) = Σ_q r_q²`. -/
theorem sum_sumPaf_eq_sq {G : Type*} [Fintype G] [AddCommGroup G] (x : Fin 4 → G → ℤ) :
    (∑ t, sumPaf x t) = ∑ q, (∑ g, x q g) ^ 2 := by
  calc (∑ t, sumPaf x t) = ∑ t : G, ∑ q : Fin 4, paf (x q) t := rfl
    _ = ∑ q : Fin 4, ∑ t : G, paf (x q) t := Finset.sum_comm
    _ = ∑ q, (∑ g, x q g) ^ 2 := Finset.sum_congr rfl fun q _ => sum_paf_eq_sq (x q)

/-- **D5** (`NOTE-B` §1.3).  Summing the house profile over the whole group gives
the second moment of the row sums:

```
Σ_q r_q² = 4n − 4s(w−1) + 4(n−w) = 8n − 4w(s+1) + 4s.
```

Only the fiber over `0` — i.e. `|K| = w` — enters; neither surjectivity of `κ`
nor the index is used. -/
theorem D5 {G Gbar : Type*} [Fintype G] [AddCommGroup G]
    [AddCommGroup Gbar] [DecidableEq Gbar] {s w : ℕ} (κ : G →+ Gbar)
    (hw : ∀ c : Gbar, (Finset.univ.filter fun g : G => κ g = c).card = w)
    (x : Fin 4 → G → ℤ) (hx : ∀ q g, IsSign (x q g)) (h2 : H2 x κ (houseM s)) :
    (∑ q, (∑ g, x q g) ^ 2)
      = 8 * (Fintype.card G : ℤ) - 4 * (w : ℤ) * ((s : ℤ) + 1) + 4 * (s : ℤ) := by
  classical
  have hker : (Finset.univ.filter fun g : G => κ g = 0).card = w := hw 0
  -- The profile, written so that the three tiers are three indicator functions.
  have hdecomp : ∀ t : G, sumPaf x t
      = 4 * (if κ t = 0 then (0 : ℤ) else 1)
        + (-4 * (s : ℤ)) * (if κ t = 0 then (1 : ℤ) else 0)
        + (4 * (Fintype.card G : ℤ) + 4 * (s : ℤ)) * (if t = 0 then (1 : ℤ) else 0) := by
    intro t
    by_cases ht : t = 0
    · subst ht
      rw [sumPaf_zero hx, map_zero]
      simp
    · by_cases hkt : κ t = 0
      · rw [h2 t ht, hkt, houseM_zero]
        simp [ht]
      · rw [h2 t ht, houseM_of_ne s hkt]
        simp [ht, hkt]
  have hstep : (∑ t : G, sumPaf x t)
      = ∑ t : G, (4 * (if κ t = 0 then (0 : ℤ) else 1)
        + (-4 * (s : ℤ)) * (if κ t = 0 then (1 : ℤ) else 0)
        + (4 * (Fintype.card G : ℤ) + 4 * (s : ℤ)) * (if t = 0 then (1 : ℤ) else 0)) :=
    Finset.sum_congr rfl fun t _ => hdecomp t
  have hsum1 : (∑ t : G, (if κ t = 0 then (1 : ℤ) else 0)) = (w : ℤ) := by
    rw [Finset.sum_boole, hker]
  have hsum0 : (∑ t : G, (if κ t = 0 then (0 : ℤ) else 1))
      = (Fintype.card G : ℤ) - (w : ℤ) := by
    have hflip : ∀ t : G,
        (if κ t = 0 then (0 : ℤ) else 1) = 1 - (if κ t = 0 then (1 : ℤ) else 0) := by
      intro t
      by_cases h : κ t = 0 <;> simp [h]
    rw [Finset.sum_congr rfl fun t (_ : t ∈ Finset.univ) => hflip t, Finset.sum_sub_distrib,
      hsum1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hsumd : (∑ t : G, (if t = 0 then (1 : ℤ) else 0)) = 1 := by
    simp
  rw [← sum_sumPaf_eq_sq, hstep, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsum0, hsum1, hsumd]
  ring

/-- **D6** (`NOTE-B` §1.3).  At index one the whole group is the kernel, so `D5`
reads `Σ_q r_q² = 4(n − ns + s)`; non-negativity of a sum of squares gives

```
n(s − 1) ≤ s.
```

For `n ≥ 3` this kills `i = 1` for every `s ≥ 2` — but that reading is prose;
what is formalized is the inequality. -/
theorem D6 {G Gbar : Type*} [Fintype G] [AddCommGroup G]
    [AddCommGroup Gbar] [DecidableEq Gbar] [Subsingleton Gbar] {s : ℕ} (κ : G →+ Gbar)
    (x : Fin 4 → G → ℤ) (hx : ∀ q g, IsSign (x q g)) (h2 : H2 x κ (houseM s)) :
    (Fintype.card G : ℤ) * ((s : ℤ) - 1) ≤ (s : ℤ) := by
  have hw : ∀ c : Gbar, (Finset.univ.filter fun g : G => κ g = c).card = Fintype.card G := by
    intro c
    rw [Finset.filter_true_of_mem fun g _ => Subsingleton.elim (κ g) c, Finset.card_univ]
  have hnn : (0 : ℤ) ≤ ∑ q, (∑ g, x q g) ^ 2 :=
    Finset.sum_nonneg fun q _ => sq_nonneg _
  rw [D5 κ hw x hx h2] at hnn
  -- The only nonlinear term is `n·s`; naming it makes the rest linear.
  obtain ⟨A, hA⟩ : ∃ A : ℤ, (Fintype.card G : ℤ) * (s : ℤ) = A := ⟨_, rfl⟩
  have hlin : 8 * (Fintype.card G : ℤ) - 4 * (Fintype.card G : ℤ) * ((s : ℤ) + 1) + 4 * (s : ℤ)
      = 4 * (Fintype.card G : ℤ) - 4 * A + 4 * (s : ℤ) := by
    rw [← hA]; ring
  have hgoal : (Fintype.card G : ℤ) * ((s : ℤ) - 1) = A - (Fintype.card G : ℤ) := by
    rw [← hA]; ring
  rw [hlin] at hnn
  rw [hgoal]
  omega

end HadamardBFormal
