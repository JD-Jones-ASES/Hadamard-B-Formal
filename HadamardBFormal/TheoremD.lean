/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import HadamardBFormal.House
import HadamardBFormal.Twist

/-!
# Theorem D: the `s = 1, i = 2` border system

`NOTE-B` §1.5.  Setting: `G` abelian of even order `n = 2w` with `w ≥ 2`, `K ≤ G` of
index two presented as a hom `κ : G →+ ZMod 2`, `s = 1`, `N = 4(n+1)`, `ε = +1` if
`κ ρ = 0` and `−1` otherwise, `σ_q(c)` the coset sums, `r_q = σ_q(0) + σ_q(1)`,
`δ_q = σ_q(0) − σ_q(1)`, `d = (δ₀, εδ₁, εδ₂, εδ₃)`.

The compared results, in the order the argument runs:

* `Lam`, `Lam_mul_transpose`, `Lam_transpose_mul`, `Lam_injective` — the `4×4` table
  `Λ(y)`, with `Λ(y)Λ(y)ᵀ = Λ(y)ᵀΛ(y) = (Σ_q y_q²)·I₄`;
* `deltaSqSum_eq_four` — `Σ_q δ_q² = 4`, the note's Parseval step; at index two the
  binding character is `±1`-valued, so this is a pure integer identity;
* `theoremD_tables` — **(D-a) + (D-b)**: `M(0) = 4`, `M(1) = ±4`, and in the genuine
  branch `M(1) = −4` the column table pair-negates onto a `4×4` Hadamard `U`;
* `theoremD_rowTable` — **(D-c)**: the row table pair-negates onto a `4×4` Hadamard
  `p`, and `E` is Hadamard;
* `theoremD_border` — **(D-d)**: (H4) collapses to `4·E = −p·Λ(d)ᵀ·U`;
* `delta_even` — the parity clause of **(D-e)**: `σ_q(c) ≡ w (mod 2)`, so `δ_q ∈ 2ℤ`.

Two devices carry the file.  `gsBlock_eval` runs the sixteen-case block bookkeeping of
the Goethals--Seidel table once, against an arbitrary functional; the two block
identities of `NOTE-B` §1.5 — the differenced table `chat_colDiff` and the summed table
`chat_rowSum` — are that one lemma applied to `B ↦ B 0 0 − B 0 1` and to
`B ↦ B 0 c + B 1 c`.  `forcing_split` isolates the integer forcing argument of (D-c)
as a statement about four integers, leaving the matrix argument as bookkeeping.

**Scope.**  This file proves the genuine branch; (D-a′), the collapse of the degenerate
branch `M = 4J₂`, is `Degenerate.lean`, which starts from this file's
`theoremD_tables_degenerate`.  The `768²` census of (D-e) is labelled
PROVEN-BY-CERTIFICATE in the note (its cert 10) and is not a theorem here.  `theoremD_transport` and the §1.6 collapse corollary are
`Collapse.lean`.
-/

namespace HadamardBFormalCore

open scoped BigOperators Matrix

/-! ### The four-by-four table `Λ` -/

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

theorem Lam_mul_transpose (y : Fin 4 → ℤ) :
    Lam y * (Lam y).transpose = (∑ q, y q * y q) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lam, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem Lam_transpose_mul (y : Fin 4 → ℤ) :
    (Lam y).transpose * Lam y = (∑ q, y q * y q) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lam, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem Lam_injective : Function.Injective Lam := by
  intro y z h
  funext q
  fin_cases q
  · exact congrFun (congrFun h 0) 0
  · exact congrFun (congrFun h 0) 1
  · exact congrFun (congrFun h 0) 2
  · exact congrFun (congrFun h 0) 3

/-! ### Sums over `ZMod 2` -/

/-- A sum over `ZMod 2` is a two-term sum.  `Fin.sum_univ_two` does not apply:
`ZMod 2` is a `Fin`-backed type but not syntactically `Fin 2`. -/
theorem zmod2_sum {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) : (∑ c, f c) = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl,
    Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]

/-- Every class is `0` or `1`. -/
theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

/-! ### `ε`, `δ`, `d` -/

/-- `ε = +1` when `κ ρ = 0` and `−1` otherwise (`NOTE-B` §1.5, setting block). -/
def eps {G : Type*} [AddCommGroup G] (κ : G →+ ZMod 2) (ρ : G) : ℤ :=
  if κ ρ = 0 then 1 else -1

@[simp]
theorem eps_of_zero {G : Type*} [AddCommGroup G] {κ : G →+ ZMod 2} {ρ : G} (h : κ ρ = 0) :
    eps κ ρ = 1 :=
  if_pos h

@[simp]
theorem eps_of_one {G : Type*} [AddCommGroup G] {κ : G →+ ZMod 2} {ρ : G} (h : κ ρ = 1) :
    eps κ ρ = -1 :=
  if_neg (by rw [h]; decide)

/-- `δ_q = σ_q(0) − σ_q(1)`, the twisted row sum. -/
def delta {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2) (x : G → ℤ) : ℤ :=
  cosetSum κ x 0 - cosetSum κ x 1

/-- `d = (δ₀, εδ₁, εδ₂, εδ₃)`, the vector the border equation of (D-d) sees. -/
def dvec {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2) (x : Fin 4 → G → ℤ) (ρ : G) :
    Fin 4 → ℤ :=
  ![delta κ (x 0), eps κ ρ * delta κ (x 1), eps κ ρ * delta κ (x 2), eps κ ρ * delta κ (x 3)]

/-! ### The binding character -/

/-- The index-two character `ψ(g) = (−1)^{κ(g)}`, bundled as an `AddChar G ℤ`. -/
def psi2 {G : Type*} [AddCommGroup G] (κ : G →+ ZMod 2) : AddChar G ℤ where
  toFun g := if κ g = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro a b
    rcases zmod2_cases (κ a) with ha | ha <;> rcases zmod2_cases (κ b) with hb | hb <;>
      simp only [map_add, ha, hb] <;> decide

@[simp]
theorem psi2_apply {G : Type*} [AddCommGroup G] (κ : G →+ ZMod 2) (g : G) :
    psi2 κ g = if κ g = 0 then 1 else -1 :=
  rfl

/-- `ψ² = 1`, the hypothesis every result of `Twist.lean` takes. -/
theorem psi2_sq {G : Type*} [AddCommGroup G] (κ : G →+ ZMod 2) (g : G) :
    psi2 κ g * psi2 κ g = 1 := by
  rcases zmod2_cases (κ g) with h | h <;> rw [psi2_apply, h] <;> decide

/-- `δ` is the `ψ`-twisted row sum: `δ = Σ_g ψ(g) x(g)`. -/
theorem delta_eq {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2) (x : G → ℤ) :
    (∑ g, psi2 κ g * x g) = delta κ x := by
  have h0 : (∑ g with κ g = (0 : ZMod 2), psi2 κ g * x g) = cosetSum κ x 0 := by
    rw [cosetSum]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [psi2_apply, if_pos (Finset.mem_filter.mp hg).2, one_mul]
  have h1 : (∑ g with κ g = (1 : ZMod 2), psi2 κ g * x g) = -cosetSum κ x 1 := by
    rw [cosetSum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [psi2_apply, if_neg (by rw [(Finset.mem_filter.mp hg).2]; decide), neg_one_mul]
  rw [← Finset.sum_fiberwise Finset.univ κ fun g => psi2 κ g * x g, zmod2_sum, h0, h1, delta,
    sub_eq_add_neg]

/-! ### `δ` is even -/

/-- A sum of signs is congruent to the number of terms, modulo two. -/
theorem sum_sign_sub_card_even {ι : Type*} (S : Finset ι) {x : ι → ℤ} (hx : ∀ i, IsSign (x i)) :
    (2 : ℤ) ∣ (∑ i ∈ S, x i) - (S.card : ℤ) := by
  have h : (∑ i ∈ S, x i) - (S.card : ℤ) = ∑ i ∈ S, (x i - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [h]
  refine Finset.dvd_sum fun i _ => ?_
  rcases hx i with h1 | h1 <;> rw [h1] <;> norm_num

/-- A coset sum is congruent to the fiber size, modulo two: `σ(c) ≡ w (mod 2)`. -/
theorem cosetSum_sub_card_even {G Gbar : Type*} [Fintype G] [DecidableEq Gbar] (κ : G → Gbar)
    {x : G → ℤ} (hx : ∀ g, IsSign (x g)) (c : Gbar) :
    (2 : ℤ) ∣ cosetSum κ x c - ((Finset.univ.filter fun g : G => κ g = c).card : ℤ) :=
  sum_sign_sub_card_even _ hx

/-- **(D-e), the parity clause.**  Each coset sum satisfies `σ_q(c) ≡ w (mod 2)`, so
`δ_q = σ_q(0) − σ_q(1)` is even.  Only equality of the two fiber sizes is used. -/
theorem delta_even {G : Type*} [Fintype G] [AddCommGroup G] {w : ℕ} (κ : G →+ ZMod 2)
    (hw : ∀ c : ZMod 2, (Finset.univ.filter fun g : G => κ g = c).card = w)
    (x : G → ℤ) (hx : ∀ g, IsSign (x g)) : Even (delta κ x) := by
  obtain ⟨k0, hk0⟩ := cosetSum_sub_card_even κ hx (0 : ZMod 2)
  obtain ⟨k1, hk1⟩ := cosetSum_sub_card_even κ hx (1 : ZMod 2)
  rw [hw 0] at hk0
  rw [hw 1] at hk1
  exact ⟨k0 - k1, by rw [delta]; omega⟩

/-! ### The integer Parseval step -/

/-- **`Σ_q δ_q² = 4`** (`NOTE-B` §1.5, (D-d)).  At index two the binding character is
`ℤ`-valued, so the note's Parseval step is a pure integer identity: `Σ_q δ_q²` is the
total mass of the `ψ`-twisted profile, and the house profile at `s = 1` evaluates it to

```
4n − 4(w−1) − 4(n−w) = 4.
```

Neither surjectivity of `κ` nor the fiber size `w` is needed: the twisted profile is
the constant `−4` off the origin, so only `|G|` enters. -/
theorem deltaSqSum_eq_four {G : Type*} [Fintype G] [AddCommGroup G]
    (κ : G →+ ZMod 2) (x : Fin 4 → G → ℤ) (hx : ∀ q g, IsSign (x q g))
    (h2 : H2 x κ (houseM 1)) :
    (∑ q, delta κ (x q) ^ 2) = 4 := by
  classical
  have hdecomp : ∀ t : G, psi2 κ t * sumPaf x t
      = -4 + (4 * (Fintype.card G : ℤ) + 4) * (if t = 0 then (1 : ℤ) else 0) := by
    intro t
    by_cases ht : t = 0
    · subst ht
      rw [sumPaf_zero hx, if_pos rfl, AddChar.map_zero_eq_one]
      ring
    · rw [h2 t ht, if_neg ht, psi2_apply]
      rcases zmod2_cases (κ t) with hk | hk
      · rw [if_pos hk, hk, houseM_zero]
        norm_num
      · rw [if_neg (by rw [hk]; decide), houseM_of_ne 1 (by rw [hk]; decide)]
        norm_num
  have hsumd : (∑ t : G, (if t = 0 then (1 : ℤ) else 0)) = 1 := by simp
  calc (∑ q, delta κ (x q) ^ 2)
      = ∑ q, (∑ g, psi2 κ g * x q g) ^ 2 :=
        Finset.sum_congr rfl fun q _ => by rw [delta_eq]
    _ = ∑ t : G, sumPaf (fun q g => psi2 κ g * x q g) t :=
        (sum_sumPaf_eq_sq fun q g => psi2 κ g * x q g).symm
    _ = ∑ t : G, psi2 κ t * sumPaf x t :=
        Finset.sum_congr rfl fun t _ => sumPaf_twist (psi2 κ) (psi2_sq κ) x t
    _ = 4 := by
        rw [Finset.sum_congr rfl fun t (_ : t ∈ Finset.univ) => hdecomp t,
          Finset.sum_add_distrib, ← Finset.mul_sum, hsumd, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
        ring

/-! ### (D-a) and (D-b): the column table -/

/-- **The Gram contraction at `(s, i) = (1, 2)`** (`NOTE-B` §1.5, the engine of (D-a)).

The Gram table is forced: `M(0) = 4` by the ansatz and `M(1) = ±4`; the reduced table
`U[I] = Q[(I,0)]` is a `4×4` Hadamard matrix; and the second row class is pinned to the
first by the **contraction** `4·Q[(I,1)] = M(1)·U[I]`.  Both branches of (D-a) read off
that one identity — `M(1) = −4` gives pair-negation (D-b), `M(1) = +4` gives
pair-equality (D-a′).

The note argues this through rank and positive semidefiniteness over `ℝ`; the proof
here is an integer one.  `U Uᵀ = 4·1` upgrades to `Matrix.IsHadamard U` by
`Matrix.IsHadamard.of_mul_conjTranspose`, whose `conjTranspose_mul` field returns
`Uᵀ U = 4·1` for free; contracting `Q[(I,1)]` against that gives the contraction, and
dotting it with `Q[(I,1)]` gives `M(1)² = 16`. -/
theorem theoremD_gramContraction (Q : Matrix (Fin 4 × ZMod 2) (Fin 4) ℤ)
    (hQ : ∀ z c, IsSign (Q z c)) (M : ZMod 2 → ℤ) (h1 : H1 (s := 1) Q M) :
    M 0 = 4 ∧ (M 1 = 4 ∨ M 1 = -4) ∧
      Matrix.IsHadamard (Matrix.of fun I c : Fin 4 => Q (I, 0) c) ∧
      ∀ I c : Fin 4, 4 * Q (I, 1) c = Q (I, 0) c * M 1 := by
  have hM0 : M 0 = 4 := by
    have h := M_zero_of_H1 hQ h1
    norm_num at h
    exact h
  have h00 : ∀ I J : Fin 4, (∑ c : Fin 4, Q (I, (0 : ZMod 2)) c * Q (J, (0 : ZMod 2)) c)
      = if I = J then (4 : ℤ) else 0 := by
    intro I J
    have h : (∑ c : Fin 4, Q (I, (0 : ZMod 2)) c * Q (J, (0 : ZMod 2)) c)
        = if I = J then M ((0 : ZMod 2) - 0) else 0 := h1 (I, 0) (J, 0)
    rwa [show ((0 : ZMod 2) - 0) = 0 from by decide, hM0] at h
  have h01 : ∀ I J : Fin 4, (∑ c : Fin 4, Q (I, (0 : ZMod 2)) c * Q (J, (1 : ZMod 2)) c)
      = if I = J then M 1 else 0 := by
    intro I J
    have h : (∑ c : Fin 4, Q (I, (0 : ZMod 2)) c * Q (J, (1 : ZMod 2)) c)
        = if I = J then M ((0 : ZMod 2) - 1) else 0 := h1 (I, 0) (J, 1)
    rwa [show ((0 : ZMod 2) - 1) = 1 from by decide] at h
  have h11 : ∀ I : Fin 4, (∑ c : Fin 4, Q (I, (1 : ZMod 2)) c * Q (I, (1 : ZMod 2)) c)
      = 4 := by
    intro I
    have h : (∑ c : Fin 4, Q (I, (1 : ZMod 2)) c * Q (I, (1 : ZMod 2)) c)
        = if I = I then M ((1 : ZMod 2) - 1) else 0 := h1 (I, 1) (I, 1)
    rwa [show ((1 : ZMod 2) - 1) = 0 from by decide, hM0, if_pos rfl] at h
  -- `U Uᵀ = 4 · 1`, hence `U` is Hadamard, hence `Uᵀ U = 4 · 1`.
  have hUUT : (Matrix.of fun I c : Fin 4 => Q (I, 0) c)
      * (Matrix.of fun I c : Fin 4 => Q (I, 0) c).transpose
      = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    ext I J
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [h00 I J]
    by_cases h : I = J
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  have hUhad : Matrix.IsHadamard (Matrix.of fun I c : Fin 4 => Q (I, 0) c) := by
    refine Matrix.IsHadamard.of_mul_conjTranspose
      (fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (hQ (i, 0) j)) ?_ ?_
    · rw [Matrix.conjTranspose_eq_transpose_of_trivial, hUUT]
      norm_num
    · rw [isRegular_iff_ne_zero]
      norm_num
  have hUTU : ∀ c c' : Fin 4, (∑ J : Fin 4, Q (J, (0 : ZMod 2)) c * Q (J, (0 : ZMod 2)) c')
      = if c = c' then (4 : ℤ) else 0 := by
    intro c c'
    have h := congrFun (congrFun hUhad.conjTranspose_mul c) c'
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply] at h
    simp only [Matrix.transpose_apply, Matrix.of_apply, Fintype.card_fin] at h
    rw [h]
    by_cases hcc : c = c'
    · rw [if_pos hcc, if_pos hcc, mul_one]
      norm_num
    · rw [if_neg hcc, if_neg hcc, mul_zero]
  -- The contraction `4 · Q[(I,1)] = M(1) · U[I]`.
  have key : ∀ I c : Fin 4,
      4 * Q (I, (1 : ZMod 2)) c = Q (I, (0 : ZMod 2)) c * M 1 := by
    intro I c
    calc 4 * Q (I, (1 : ZMod 2)) c
        = ∑ c' : Fin 4, (if c = c' then (4 : ℤ) else 0) * Q (I, (1 : ZMod 2)) c' := by simp
      _ = ∑ c' : Fin 4, ∑ J : Fin 4,
            Q (J, (0 : ZMod 2)) c * (Q (J, (0 : ZMod 2)) c' * Q (I, (1 : ZMod 2)) c') := by
          refine Finset.sum_congr rfl fun c' _ => ?_
          rw [← hUTU c c', Finset.sum_mul]
          exact Finset.sum_congr rfl fun J _ => by ring
      _ = ∑ J : Fin 4, ∑ c' : Fin 4,
            Q (J, (0 : ZMod 2)) c * (Q (J, (0 : ZMod 2)) c' * Q (I, (1 : ZMod 2)) c') :=
          Finset.sum_comm
      _ = ∑ J : Fin 4, Q (J, (0 : ZMod 2)) c * (if J = I then M 1 else 0) := by
          refine Finset.sum_congr rfl fun J _ => ?_
          rw [← Finset.mul_sum, h01 J I]
      _ = Q (I, (0 : ZMod 2)) c * M 1 := by simp
  -- Dotting the contraction with `Q[(I,1)]` gives `M(1)² = 16`.
  have hsq : M 1 * M 1 = 16 := by
    have hL : (∑ c : Fin 4,
        4 * Q ((0 : Fin 4), (1 : ZMod 2)) c * Q ((0 : Fin 4), (1 : ZMod 2)) c) = 16 := by
      rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) =>
          mul_assoc (4 : ℤ) (Q ((0 : Fin 4), (1 : ZMod 2)) c) (Q ((0 : Fin 4), (1 : ZMod 2)) c),
        ← Finset.mul_sum, h11 0]
      norm_num
    have hR : (∑ c : Fin 4,
        Q ((0 : Fin 4), (0 : ZMod 2)) c * M 1 * Q ((0 : Fin 4), (1 : ZMod 2)) c)
          = M 1 * M 1 := by
      have hstep : ∀ c : Fin 4,
          Q ((0 : Fin 4), (0 : ZMod 2)) c * M 1 * Q ((0 : Fin 4), (1 : ZMod 2)) c
            = M 1 * (Q ((0 : Fin 4), (0 : ZMod 2)) c * Q ((0 : Fin 4), (1 : ZMod 2)) c) :=
        fun c => by ring
      rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => hstep c, ← Finset.mul_sum,
        h01 0 0, if_pos rfl]
    rw [← hR, ← hL]
    exact Finset.sum_congr rfl fun c _ => by rw [key 0 c]
  have hM1 : M 1 = 4 ∨ M 1 = -4 := by
    have hfac : (M 1 - 4) * (M 1 + 4) = M 1 * M 1 - 16 := by ring
    have h : (M 1 - 4) * (M 1 + 4) = 0 := by rw [hfac, hsq]; norm_num
    rcases mul_eq_zero.mp h with h' | h'
    · left; linarith
    · right; linarith
  exact ⟨hM0, hM1, hUhad, key⟩

/-- **Theorem D, clauses (D-a) and (D-b)** (`NOTE-B` §1.5).

At `(s, i) = (1, 2)` the Gram table is forced: `M(0) = 4` by the ansatz and
`M(1) = ±4`.  In the genuine branch `M(1) = −4` the column table pair-negates,
`Q[(I,1)] = −Q[(I,0)]`, and the reduced table `U[I] = Q[(I,0)]` is a `4×4`
Hadamard matrix.  This is `theoremD_gramContraction` read at `M(1) = −4`. -/
theorem theoremD_tables (Q : Matrix (Fin 4 × ZMod 2) (Fin 4) ℤ) (hQ : ∀ z c, IsSign (Q z c))
    (M : ZMod 2 → ℤ) (h1 : H1 (s := 1) Q M) :
    M 0 = 4 ∧ (M 1 = 4 ∨ M 1 = -4) ∧
      (M 1 = -4 →
        (∀ I : Fin 4, Q (I, 1) = -Q (I, 0)) ∧
          Matrix.IsHadamard (Matrix.of fun I c : Fin 4 => Q (I, 0) c)) := by
  obtain ⟨hM0, hM1, hUhad, key⟩ := theoremD_gramContraction Q hQ M h1
  refine ⟨hM0, hM1, fun hneg => ⟨fun I => ?_, hUhad⟩⟩
  funext c
  have h := key I c
  rw [hneg] at h
  change Q (I, (1 : ZMod 2)) c = -Q (I, (0 : ZMod 2)) c
  linarith

/-- **Theorem D, clause (D-a′), first item** (`NOTE-B` §1.5).  In the degenerate branch
`M(1) = +4` the same contraction forces the column table to pair up **equal**,
`Q[(I,1)] = Q[(I,0)]`, and `U[I] = Q[(I,0)]` is again a `4×4` Hadamard matrix.  This is
(D-b) with the sign reversed: `+4` forces equality where `−4` forces negation. -/
theorem theoremD_tables_degenerate (Q : Matrix (Fin 4 × ZMod 2) (Fin 4) ℤ)
    (hQ : ∀ z c, IsSign (Q z c)) (M : ZMod 2 → ℤ) (h1 : H1 (s := 1) Q M) (hpos : M 1 = 4) :
    (∀ I : Fin 4, Q (I, 1) = Q (I, 0)) ∧
      Matrix.IsHadamard (Matrix.of fun I c : Fin 4 => Q (I, 0) c) := by
  obtain ⟨-, -, hUhad, key⟩ := theoremD_gramContraction Q hQ M h1
  refine ⟨fun I => ?_, hUhad⟩
  funext c
  have h := key I c
  rw [hpos] at h
  change Q (I, (1 : ZMod 2)) c = Q (I, (0 : ZMod 2)) c
  linarith

/-! ### Evaluating a functional on the Goethals--Seidel table

The two block identities of `NOTE-B` §1.5 -- the differenced table `Λ(d)` of (D-d)
and the summed table `Λ(r)` of (D-a′)/(D-c) -- are the *same* sixteen-case
bookkeeping run against different functionals.  `gsBlock_eval` runs it once. -/

/-- If a sign-respecting functional `L` takes the value `y 0` on the plain block and
the value `y q` on both reversed shapes of the `q`-th block, then it takes the value
`Λ(y)[I,J]` on every one of the sixteen positions of the Goethals--Seidel table. -/
theorem gsBlock_eval {Gb : Type*} (r : Equiv.Perm Gb) (X : Fin 4 → Matrix Gb Gb ℤ)
    (L : Matrix Gb Gb ℤ → ℤ) (hneg : ∀ A, L (-A) = -L A) (y : Fin 4 → ℤ)
    (hp : L (X 0) = y 0)
    (hr1 : L (revCols r (X 1)) = y 1) (hr2 : L (revCols r (X 2)) = y 2)
    (hr3 : L (revCols r (X 3)) = y 3)
    (ht1 : L (revCols r ((X 1).transpose)) = y 1)
    (ht2 : L (revCols r ((X 2).transpose)) = y 2)
    (ht3 : L (revCols r ((X 3).transpose)) = y 3)
    (I J : Fin 4) : L (gsBlock r X I J) = Lam y I J := by
  fin_cases I <;> fin_cases J <;>
    simp only [gsBlock, Lam, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.of_apply,
      hneg, hp, hr1, hr2, hr3, ht1, ht2, ht3]

/-- `Λ` is odd. -/
theorem Lam_neg (y : Fin 4 → ℤ) : Lam (fun q => -y q) = -Lam y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lam]

/-! ### The two compressed-block identities

`NOTE-B` §1.5, the two displays of (D-a′): differencing the columns of a block of
`Ĉ` gives `Λ(d)`, summing its rows gives `Λ(r)`. -/

/-- The two fibers of `κ` partition `G`. -/
theorem cosetSum_add_cosetSum {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) : cosetSum κ y 0 + cosetSum κ y 1 = ∑ g, y g := by
  rw [← Finset.sum_fiberwise Finset.univ κ y, zmod2_sum]
  rfl

/-- Two coset sums at distinct classes add up to the row sum. -/
theorem cosetSum_pair_add {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) {a b : ZMod 2} (hab : a ≠ b) :
    cosetSum κ y a + cosetSum κ y b = ∑ g, y g := by
  rcases zmod2_cases a with ha | ha <;> rcases zmod2_cases b with hb | hb <;> subst ha <;> subst hb
  · exact absurd rfl hab
  · exact cosetSum_add_cosetSum κ y
  · rw [add_comm]
    exact cosetSum_add_cosetSum κ y
  · exact absurd rfl hab

/-- The `ε`-twisted difference of coset sums along the reflection shift. -/
theorem cosetSum_shift_diff {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) (ρ : G) :
    cosetSum κ y (κ ρ) - cosetSum κ y (κ ρ - 1) = eps κ ρ * delta κ y := by
  rcases zmod2_cases (κ ρ) with h | h
  · rw [h, show ((0 : ZMod 2) - 1) = 1 from by decide, eps_of_zero h, delta, one_mul]
  · rw [h, show ((1 : ZMod 2) - 1) = 0 from by decide, eps_of_one h, delta]
    ring

/-- Row sums of the seed quadruple. -/
def rvec {G : Type*} [Fintype G] (x : Fin 4 → G → ℤ) : Fin 4 → ℤ :=
  fun q => ∑ g, x q g

/-! #### The summed table -/

/-- Summing a plain compressed block over the two rows gives the row sum. -/
theorem chatShape_sum_plain {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) (c : ZMod 2) :
    dev (cosetSum κ y) 0 c + dev (cosetSum κ y) 1 c = ∑ g, y g := by
  simp only [dev_apply]
  exact cosetSum_pair_add κ y (by revert c; decide)

/-- Summing a reversed compressed block over the two rows gives the row sum. -/
theorem chatShape_sum_rev {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) (ρ : G) (c : ZMod 2) :
    revCols (reflect (κ ρ)) (dev (cosetSum κ y)) 0 c
      + revCols (reflect (κ ρ)) (dev (cosetSum κ y)) 1 c = ∑ g, y g := by
  have hne : ∀ k : ZMod 2, k - 0 ≠ k - 1 := by decide
  simp only [revCols_apply, reflect_apply, dev_apply]
  exact cosetSum_pair_add κ y (hne (κ ρ - c))

/-- Summing a transposed reversed compressed block over the two rows gives the row sum. -/
theorem chatShape_sum_revT {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) (ρ : G) (c : ZMod 2) :
    revCols (reflect (κ ρ)) ((dev (cosetSum κ y)).transpose) 0 c
      + revCols (reflect (κ ρ)) ((dev (cosetSum κ y)).transpose) 1 c = ∑ g, y g := by
  have hne : ∀ k : ZMod 2, (0 : ZMod 2) - k ≠ 1 - k := by decide
  simp only [revCols_apply, Matrix.transpose_apply, reflect_apply, dev_apply]
  exact cosetSum_pair_add κ y (hne (κ ρ - c))

/-- **The summed table** (`NOTE-B` §1.5, second display of (D-a′)).  Adding the two
rows of a block of `Ĉ` gives `Λ(r)`, whatever the column class.  No `ε` enters. -/
theorem chat_rowSum {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (x : Fin 4 → G → ℤ) (ρ : G) (I J : Fin 4) (c : ZMod 2) :
    chat κ x ρ (I, 0) (J, c) + chat κ x ρ (I, 1) (J, c) = Lam (rvec x) I J := by
  refine gsBlock_eval (reflect (κ ρ)) (fun q => dev (cosetSum κ (x q)))
    (fun B => B 0 c + B 1 c) (fun A => by simp only [Matrix.neg_apply]; ring) (rvec x)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ I J
  · exact chatShape_sum_plain κ (x 0) c
  · exact chatShape_sum_rev κ (x 1) ρ c
  · exact chatShape_sum_rev κ (x 2) ρ c
  · exact chatShape_sum_rev κ (x 3) ρ c
  · exact chatShape_sum_revT κ (x 1) ρ c
  · exact chatShape_sum_revT κ (x 2) ρ c
  · exact chatShape_sum_revT κ (x 3) ρ c

/-! #### The differenced table -/

/-- Differencing the columns of a plain compressed block at row `0` gives `δ`. -/
theorem chatShape_diff_plain {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) :
    dev (cosetSum κ y) 0 0 - dev (cosetSum κ y) 0 1 = delta κ y := by
  simp only [dev_apply]
  rw [show ((0 : ZMod 2) - 0) = 0 from by decide, show ((1 : ZMod 2) - 0) = 1 from by decide,
    delta]

/-- Differencing the columns of a reversed compressed block at row `0` gives `εδ`. -/
theorem chatShape_diff_rev {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) (ρ : G) :
    revCols (reflect (κ ρ)) (dev (cosetSum κ y)) 0 0
      - revCols (reflect (κ ρ)) (dev (cosetSum κ y)) 0 1 = eps κ ρ * delta κ y := by
  have e1 : ∀ k : ZMod 2, k - 0 - 0 = k := by decide
  have e2 : ∀ k : ZMod 2, k - 1 - 0 = k - 1 := by decide
  simp only [revCols_apply, reflect_apply, dev_apply]
  rw [e1 (κ ρ), e2 (κ ρ)]
  exact cosetSum_shift_diff κ y ρ

/-- Differencing the columns of a transposed reversed block at row `0` gives `εδ`. -/
theorem chatShape_diff_revT {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) (ρ : G) :
    revCols (reflect (κ ρ)) ((dev (cosetSum κ y)).transpose) 0 0
      - revCols (reflect (κ ρ)) ((dev (cosetSum κ y)).transpose) 0 1 = eps κ ρ * delta κ y := by
  have e1 : ∀ k : ZMod 2, (0 : ZMod 2) - (k - 0) = k := by decide
  have e2 : ∀ k : ZMod 2, (0 : ZMod 2) - (k - 1) = k - 1 := by decide
  simp only [revCols_apply, Matrix.transpose_apply, reflect_apply, dev_apply]
  rw [e1 (κ ρ), e2 (κ ρ)]
  exact cosetSum_shift_diff κ y ρ

/-- The same three shapes at row `1`, where every value is negated. -/
theorem chatShape_diffOne_plain {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) :
    dev (cosetSum κ y) 1 0 - dev (cosetSum κ y) 1 1 = -delta κ y := by
  simp only [dev_apply]
  rw [show ((0 : ZMod 2) - 1) = 1 from by decide, show ((1 : ZMod 2) - 1) = 0 from by decide,
    delta]
  ring

theorem chatShape_diffOne_rev {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) (ρ : G) :
    revCols (reflect (κ ρ)) (dev (cosetSum κ y)) 1 0
      - revCols (reflect (κ ρ)) (dev (cosetSum κ y)) 1 1 = -(eps κ ρ * delta κ y) := by
  have e1 : ∀ k : ZMod 2, k - 0 - 1 = k - 1 := by decide
  have e2 : ∀ k : ZMod 2, k - 1 - 1 = k := by decide
  have h := cosetSum_shift_diff κ y ρ
  simp only [revCols_apply, reflect_apply, dev_apply]
  rw [e1 (κ ρ), e2 (κ ρ)]
  linarith

theorem chatShape_diffOne_revT {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) (ρ : G) :
    revCols (reflect (κ ρ)) ((dev (cosetSum κ y)).transpose) 1 0
      - revCols (reflect (κ ρ)) ((dev (cosetSum κ y)).transpose) 1 1
      = -(eps κ ρ * delta κ y) := by
  have e1 : ∀ k : ZMod 2, (1 : ZMod 2) - (k - 0) = k - 1 := by decide
  have e2 : ∀ k : ZMod 2, (1 : ZMod 2) - (k - 1) = k := by decide
  have h := cosetSum_shift_diff κ y ρ
  simp only [revCols_apply, Matrix.transpose_apply, reflect_apply, dev_apply]
  rw [e1 (κ ρ), e2 (κ ρ)]
  linarith

/-- **The differenced table** (`NOTE-B` §1.5, (D-d)).  `D_I[J] = Ĉ[(I,0),(J,0)] −
Ĉ[(I,0),(J,1)]` is `Λ(d)` exactly -- the identity that turns (H4) into a single `4×4`
equation.  This is where `ε` enters: a plain block contributes `δ_q`, a reflected or
transposed-reflected one contributes `εδ_q`. -/
theorem chat_colDiff {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (x : Fin 4 → G → ℤ) (ρ : G) (I J : Fin 4) :
    chat κ x ρ (I, 0) (J, 0) - chat κ x ρ (I, 0) (J, 1) = Lam (dvec κ x ρ) I J := by
  refine gsBlock_eval (reflect (κ ρ)) (fun q => dev (cosetSum κ (x q)))
    (fun B => B 0 0 - B 0 1) (fun A => by simp only [Matrix.neg_apply]; ring) (dvec κ x ρ)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ I J
  · exact chatShape_diff_plain κ (x 0)
  · exact chatShape_diff_rev κ (x 1) ρ
  · exact chatShape_diff_rev κ (x 2) ρ
  · exact chatShape_diff_rev κ (x 3) ρ
  · exact chatShape_diff_revT κ (x 1) ρ
  · exact chatShape_diff_revT κ (x 2) ρ
  · exact chatShape_diff_revT κ (x 3) ρ

/-- The differenced table at the second row class: `−Λ(d)`. -/
theorem chat_colDiff_one {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (x : Fin 4 → G → ℤ) (ρ : G) (I J : Fin 4) :
    chat κ x ρ (I, 1) (J, 0) - chat κ x ρ (I, 1) (J, 1) = -Lam (dvec κ x ρ) I J := by
  have h : (fun B : Matrix (ZMod 2) (ZMod 2) ℤ => B 1 0 - B 1 1)
      (gsBlock (reflect (κ ρ)) (fun q => dev (cosetSum κ (x q))) I J)
      = Lam (fun q => -dvec κ x ρ q) I J := by
    refine gsBlock_eval (reflect (κ ρ)) (fun q => dev (cosetSum κ (x q)))
      (fun B => B 1 0 - B 1 1) (fun A => by simp only [Matrix.neg_apply]; ring)
      (fun q => -dvec κ x ρ q) ?_ ?_ ?_ ?_ ?_ ?_ ?_ I J
    · exact chatShape_diffOne_plain κ (x 0)
    · exact chatShape_diffOne_rev κ (x 1) ρ
    · exact chatShape_diffOne_rev κ (x 2) ρ
    · exact chatShape_diffOne_rev κ (x 3) ρ
    · exact chatShape_diffOne_revT κ (x 1) ρ
    · exact chatShape_diffOne_revT κ (x 2) ρ
    · exact chatShape_diffOne_revT κ (x 3) ρ
  rw [Lam_neg] at h
  exact h

/-! ### The scalar forcing lemma behind (D-c)

`NOTE-B` §1.5, (D-c): "entries of `p pᵀ` are even, `|E Eᵀ|_off ≤ 4s`, `w > 2s`,
therefore both are zero".  Isolated as an arithmetic statement so that the matrix
argument is pure bookkeeping. -/

/-- If `a + w·b = 0` with `b` even, `|a| ≤ 4s` and `w > 2s ≥ 0`, then both vanish. -/
theorem forcing_split (a b w s : ℤ) (hb : Even b) (ha : |a| ≤ 4 * s) (h : a + w * b = 0)
    (hw : 2 * s < w) (hs : 0 ≤ s) : b = 0 ∧ a = 0 := by
  obtain ⟨k, rfl⟩ := hb
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  have hwpos : (0 : ℤ) ≤ w := by omega
  have hk : k = 0 := by
    rcases lt_trichotomy k 0 with hneg | hzero | hpos
    · exfalso
      have hle : w * (k + k) ≤ w * (-2) := by
        refine mul_le_mul_of_nonneg_left ?_ hwpos
        omega
      omega
    · exact hzero
    · exfalso
      have hle : w * 2 ≤ w * (k + k) := by
        refine mul_le_mul_of_nonneg_left ?_ hwpos
        omega
      omega
  subst hk
  refine ⟨by omega, ?_⟩
  simpa using h

/-! ### Elementary sign estimates -/

/-- A sum of products of signs is bounded by the number of terms. -/
theorem abs_sum_sign_le {ι : Type*} (S : Finset ι) {u v : ι → ℤ} (hu : ∀ i, IsSign (u i))
    (hv : ∀ i, IsSign (v i)) : |∑ i ∈ S, u i * v i| ≤ (S.card : ℤ) := by
  have hone : ∀ i ∈ S, |u i * v i| = 1 := by
    intro i _
    rcases hu i with h | h <;> rcases hv i with h' | h' <;> rw [h, h'] <;> norm_num
  calc |∑ i ∈ S, u i * v i| ≤ ∑ i ∈ S, |u i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ _i ∈ S, (1 : ℤ) := Finset.sum_congr rfl hone
    _ = (S.card : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A sum of squares of signs is the number of terms. -/
theorem sum_sign_mul_self {ι : Type*} (S : Finset ι) {u : ι → ℤ} (hu : ∀ i, IsSign (u i)) :
    (∑ i ∈ S, u i * u i) = (S.card : ℤ) := by
  have hone : ∀ i ∈ S, u i * u i = 1 := by
    intro i _
    rcases hu i with h | h <;> rw [h] <;> norm_num
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A sum of products of signs has the parity of the number of terms. -/
theorem even_sum_sign {ι : Type*} (S : Finset ι) {u v : ι → ℤ} (hu : ∀ i, IsSign (u i))
    (hv : ∀ i, IsSign (v i)) (hcard : Even (S.card : ℤ)) : Even (∑ i ∈ S, u i * v i) := by
  obtain ⟨m, hm⟩ := sum_sign_sub_card_even S (x := fun i => u i * v i)
    fun i => (hu i).mul (hv i)
  obtain ⟨j, hj⟩ := hcard
  exact ⟨m + j, by omega⟩

/-! ### (D-c): the row table -/

/-- **Theorem D, clause (D-c)** (`NOTE-B` §1.5).

Once the column table has pair-negated, (H4) forces the row table to pair-negate too:
summing the two rows of a block of `Ĉ` gives `Λ(r)`, `D5` gives `Σ_q r_q² = N ≠ 0` so
`Λ(r)` is nonsingular, and the column sums `P[r][2J] + P[r][2J+1]` are annihilated.
The doubling then turns (H3) into `E Eᵀ + 2w·p pᵀ = N·I₄`, and the integer forcing
lemma splits it: `p` is a `4×4` Hadamard matrix and so is `E`.

This is sharper than `D3`, which needs `w > 2s`: the doubling turned `w` into `2w`,
so `w ≥ 2` suffices. -/
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
  -- The index-two arithmetic `n = 2w`, which turns `D5` into `Σ_q r_q² = N`.
  have hn : (Fintype.card G : ℤ) = 2 * (w : ℤ) := by
    have h := sum_comp_of_card_fiber_eq (⇑κ) hw fun _ => (1 : ℤ)
    rw [zmod2_sum] at h
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
    rw [h]
    ring
  have hQp : ∀ I c : Fin 4, Q (I, (1 : ZMod 2)) c = -Q (I, (0 : ZMod 2)) c := by
    intro I c
    rw [hQpair I]
    rfl
  -- (H4), entrywise.
  have h4' : ∀ (r I : Fin 4) (c : ZMod 2),
      (∑ e : Fin 4, E r e * Q (I, c) e)
        + ∑ J : Fin 4, ∑ b : ZMod 2, P r (J, b) * chat κ x ρ (I, c) (J, b) = 0 := by
    intro r I c
    have h := congrFun (congrFun h4 r) ((I, c) : Fin 4 × ZMod 2)
    simpa only [Matrix.add_apply, Matrix.zero_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_prod_type] using h
  -- Adding the two row classes kills the corner and leaves `Λ(r)·a_r = 0`.
  have hLamAnn : ∀ r I : Fin 4,
      (∑ J : Fin 4, (P r (J, 0) + P r (J, 1)) * Lam (rvec x) I J) = 0 := by
    intro r I
    have h0 := h4' r I 0
    have h1 := h4' r I 1
    have hEcancel : (∑ e : Fin 4, E r e * Q (I, (0 : ZMod 2)) e)
        + (∑ e : Fin 4, E r e * Q (I, (1 : ZMod 2)) e) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [hQp I e]
      ring
    have hCJ : ∀ J : Fin 4,
        (∑ b : ZMod 2, P r (J, b) * chat κ x ρ (I, 0) (J, b))
          + (∑ b : ZMod 2, P r (J, b) * chat κ x ρ (I, 1) (J, b))
          = (P r (J, 0) + P r (J, 1)) * Lam (rvec x) I J := by
      intro J
      rw [← Finset.sum_add_distrib]
      calc (∑ b : ZMod 2, (P r (J, b) * chat κ x ρ (I, 0) (J, b)
              + P r (J, b) * chat κ x ρ (I, 1) (J, b)))
          = ∑ b : ZMod 2, P r (J, b) * Lam (rvec x) I J := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [← mul_add, chat_rowSum κ x ρ I J b]
        _ = (∑ b : ZMod 2, P r (J, b)) * Lam (rvec x) I J := by rw [Finset.sum_mul]
        _ = (P r (J, 0) + P r (J, 1)) * Lam (rvec x) I J := by rw [zmod2_sum]
    have hzero : (∑ J : Fin 4, ∑ b : ZMod 2, P r (J, b) * chat κ x ρ (I, 0) (J, b))
        + (∑ J : Fin 4, ∑ b : ZMod 2, P r (J, b) * chat κ x ρ (I, 1) (J, b)) = 0 := by
      linarith
    rw [← hzero, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun J _ => (hCJ J).symm
  -- `D5` at the house profile: `Σ_q r_q² = N`.
  have hN : (∑ q, rvec x q * rvec x q) = 4 * ((Fintype.card G : ℤ) + 1) := by
    have hd5 := D5 κ (hw 0) x hx h2
    have hcvt : (∑ q, rvec x q * rvec x q) = ∑ q, (∑ g, x q g) ^ 2 :=
      Finset.sum_congr rfl fun q _ => by simp only [rvec]; ring
    rw [hcvt, hd5, hn]
    push_cast
    ring
  have hNpos : (0 : ℤ) < 4 * ((Fintype.card G : ℤ) + 1) := by
    have hc : (0 : ℤ) ≤ (Fintype.card G : ℤ) := Int.natCast_nonneg _
    linarith
  have hLT : ∀ J0 J : Fin 4, (∑ I : Fin 4, Lam (rvec x) I J0 * Lam (rvec x) I J)
      = if J0 = J then 4 * ((Fintype.card G : ℤ) + 1) else 0 := by
    intro J0 J
    have h := congrFun (congrFun (Lam_transpose_mul (rvec x)) J0) J
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at h
    simp only [Matrix.transpose_apply] at h
    rw [hN] at h
    rw [h]
    by_cases hJ : J0 = J
    · rw [if_pos hJ, if_pos hJ, mul_one]
    · rw [if_neg hJ, if_neg hJ, mul_zero]
  -- `Λ(r)` is nonsingular, so the column sums of `P` vanish.
  have hPsum : ∀ r J : Fin 4, P r (J, 0) + P r (J, 1) = 0 := by
    intro r J0
    have hkill : 4 * ((Fintype.card G : ℤ) + 1) * (P r (J0, 0) + P r (J0, 1)) = 0 := by
      calc 4 * ((Fintype.card G : ℤ) + 1) * (P r (J0, 0) + P r (J0, 1))
          = ∑ J : Fin 4, (if J0 = J then 4 * ((Fintype.card G : ℤ) + 1) else 0)
              * (P r (J, 0) + P r (J, 1)) := by simp
        _ = ∑ J : Fin 4, ∑ I : Fin 4,
              Lam (rvec x) I J0 * ((P r (J, 0) + P r (J, 1)) * Lam (rvec x) I J) := by
            refine Finset.sum_congr rfl fun J _ => ?_
            rw [← hLT J0 J, Finset.sum_mul]
            exact Finset.sum_congr rfl fun I _ => by ring
        _ = ∑ I : Fin 4, ∑ J : Fin 4,
              Lam (rvec x) I J0 * ((P r (J, 0) + P r (J, 1)) * Lam (rvec x) I J) :=
            Finset.sum_comm
        _ = ∑ I : Fin 4, Lam (rvec x) I J0
              * ∑ J : Fin 4, (P r (J, 0) + P r (J, 1)) * Lam (rvec x) I J :=
            Finset.sum_congr rfl fun I _ => (Finset.mul_sum _ _ _).symm
        _ = 0 := Finset.sum_eq_zero fun I _ => by rw [hLamAnn r I, mul_zero]
    rcases mul_eq_zero.mp hkill with h' | h'
    · exact absurd h' (by linarith)
    · exact h'
  have hPp : ∀ r J : Fin 4, P r (J, 1) = -P r (J, 0) := by
    intro r J
    have h := hPsum r J
    linarith
  -- The doubling turns (H3) into `E Eᵀ + 2w·p pᵀ = N·I₄`.
  have hPPT : ∀ r t : Fin 4, (∑ z : Fin 4 × ZMod 2, P r z * P t z)
      = 2 * ∑ J : Fin 4, P r (J, 0) * P t (J, 0) := by
    intro r t
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [zmod2_sum, hPp r J, hPp t J]
    ring
  have h3' : ∀ r t : Fin 4, (∑ e : Fin 4, E r e * E t e)
      + (2 * (w : ℤ)) * (∑ J : Fin 4, P r (J, 0) * P t (J, 0))
      = 4 * ((Fintype.card G : ℤ) + 1) * (if r = t then 1 else 0) := by
    intro r t
    have h := congrFun (congrFun h3 r) t
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply] at h
    rw [hPPT r t] at h
    rw [← h]
    ring
  have hoff : ∀ r t : Fin 4, r ≠ t →
      (∑ J : Fin 4, P r (J, 0) * P t (J, 0)) = 0 ∧ (∑ e : Fin 4, E r e * E t e) = 0 := by
    intro r t hrt
    have h := h3' r t
    rw [if_neg hrt, mul_zero] at h
    refine forcing_split _ _ (2 * (w : ℤ)) 1 ?_ ?_ h ?_ (by norm_num)
    · refine even_sum_sign _ (fun J => hP r (J, 0)) (fun J => hP t (J, 0)) ?_
      simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
      exact ⟨2, by norm_num⟩
    · have hb := abs_sum_sign_le (Finset.univ : Finset (Fin 4)) (fun e => hE r e)
        fun e => hE t e
      simpa using hb
    · have hwc : (2 : ℤ) ≤ (w : ℤ) := by exact_mod_cast hw2
      linarith
  have hEdiag : ∀ r : Fin 4, (∑ e : Fin 4, E r e * E r e) = 4 := by
    intro r
    simpa using sum_sign_mul_self (Finset.univ : Finset (Fin 4)) fun e => hE r e
  have hPdiag : ∀ r : Fin 4, (∑ J : Fin 4, P r (J, 0) * P r (J, 0)) = 4 := by
    intro r
    simpa using sum_sign_mul_self (Finset.univ : Finset (Fin 4)) fun J => hP r (J, 0)
  have hEE : E * E.transpose = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    ext r t
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    simp only [Matrix.transpose_apply]
    by_cases hrt : r = t
    · subst hrt
      rw [if_pos rfl, mul_one]
      exact hEdiag r
    · rw [if_neg hrt, mul_zero]
      exact (hoff r t hrt).2
  have hpp : (Matrix.of fun r J : Fin 4 => P r (J, 0))
      * (Matrix.of fun r J : Fin 4 => P r (J, 0)).transpose
      = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    ext r t
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    by_cases hrt : r = t
    · subst hrt
      rw [if_pos rfl, mul_one]
      exact hPdiag r
    · rw [if_neg hrt, mul_zero]
      exact (hoff r t hrt).1
  refine ⟨hPp, ?_, ?_⟩
  · refine Matrix.IsHadamard.of_mul_conjTranspose
      (fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (hP i (j, 0))) ?_ ?_
    · rw [Matrix.conjTranspose_eq_transpose_of_trivial, hpp]
      norm_num
    · rw [isRegular_iff_ne_zero]
      norm_num
  · refine Matrix.IsHadamard.of_mul_conjTranspose
      (fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (hE i j)) ?_ ?_
    · rw [Matrix.conjTranspose_eq_transpose_of_trivial, hEE]
      norm_num
    · rw [isRegular_iff_ne_zero]
      norm_num

/-! ### (D-d): the border equation -/

/-- **Theorem D, clause (D-d)** (`NOTE-B` §1.5).

With the two tables pair-negated and `U` Hadamard, (H4) -- a `4 × 8` condition --
collapses to the single `4 × 4` equation

```
E Uᵀ + p Λ(d)ᵀ = 0,   equivalently   4·E = −p·Λ(d)ᵀ·U.
```

The engine is `chat_colDiff`: the differenced block table of `Ĉ` **is** `Λ(d)`.  The
`4 •` form keeps everything in `ℤ` where the note writes `E = −¼·p·Λ(d)ᵀ·U`.

The second row class carries no further information: by `chat_colDiff_one` its
equation is the negative of the first. -/
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
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix (Fin 4) (Fin 4) ℤ,
      U = Matrix.of fun I c : Fin 4 => Q (I, 0) c := ⟨_, rfl⟩
  obtain ⟨p, hpdef⟩ : ∃ p : Matrix (Fin 4) (Fin 4) ℤ,
      p = Matrix.of fun r J : Fin 4 => P r (J, 0) := ⟨_, rfl⟩
  have hUe : ∀ I c : Fin 4, U I c = Q (I, 0) c := by
    rw [hUdef]
    exact fun _ _ => rfl
  have hpe : ∀ r J : Fin 4, p r J = P r (J, 0) := by
    rw [hpdef]
    exact fun _ _ => rfl
  rw [← hUdef] at hU
  rw [← hUdef, ← hpdef]
  have hQe : ∀ I c : Fin 4, Q (I, (1 : ZMod 2)) c = -U I c := by
    intro I c
    rw [hUe, hQpair I]
    rfl
  have hUUT : U * U.transpose = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    have h := hU.mul_conjTranspose
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    simpa using h
  have hUTU : U.transpose * U = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    have h := hU.conjTranspose_mul
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    simpa using h
  -- (H4), entry by entry, is the single `4 × 4` equation up to a sign.
  have hEnt : ∀ (r I : Fin 4) (c : ZMod 2),
      (E * Q.transpose + P * (chat κ x ρ).transpose) r (I, c)
        = (if c = 0 then (1 : ℤ) else -1)
            * ((E * U.transpose + p * (Lam (dvec κ x ρ)).transpose) r I) := by
    intro r I c
    have hExp : (E * Q.transpose + P * (chat κ x ρ).transpose) r (I, c)
        = (∑ e : Fin 4, E r e * Q (I, c) e)
          + ∑ J : Fin 4, ∑ b : ZMod 2, P r (J, b) * chat κ x ρ (I, c) (J, b) := by
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Fintype.sum_prod_type]
    have hRHS : (E * U.transpose + p * (Lam (dvec κ x ρ)).transpose) r I
        = (∑ e : Fin 4, E r e * U I e) + ∑ J : Fin 4, p r J * Lam (dvec κ x ρ) I J := by
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
    rw [hExp, hRHS]
    rcases zmod2_cases c with hc | hc <;> subst hc
    · rw [if_pos rfl, one_mul]
      congr 1
      · exact Finset.sum_congr rfl fun e _ => by rw [hUe]
      · refine Finset.sum_congr rfl fun J _ => ?_
        rw [zmod2_sum, hPpair r J, hpe r J, ← chat_colDiff κ x ρ I J]
        ring
    · rw [if_neg (by decide), neg_one_mul, neg_add]
      congr 1
      · rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun e _ => by rw [hQe I e]; ring
      · rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun J _ => ?_
        have hL : Lam (dvec κ x ρ) I J
            = -(chat κ x ρ (I, 1) (J, 0) - chat κ x ρ (I, 1) (J, 1)) := by
          rw [chat_colDiff_one κ x ρ I J]
          ring
        rw [zmod2_sum, hPpair r J, hpe r J, hL]
        ring
  have hA : H4 (s := 1) E P Q (chat κ x ρ) ↔
      E * U.transpose + p * (Lam (dvec κ x ρ)).transpose = 0 := by
    constructor
    · intro h4
      ext r I
      have h := congrFun (congrFun h4 r) ((I, (0 : ZMod 2)) : Fin 4 × ZMod 2)
      rw [Matrix.zero_apply, hEnt r I 0, if_pos rfl, one_mul] at h
      rw [Matrix.zero_apply]
      exact h
    · intro hz
      ext r z
      obtain ⟨I, c⟩ := z
      have h := congrFun (congrFun hz r) I
      rw [Matrix.zero_apply] at h
      rw [Matrix.zero_apply, hEnt r I c, h, mul_zero]
  rw [hA]
  constructor
  · intro h
    have h' : (E * U.transpose + p * (Lam (dvec κ x ρ)).transpose) * U
        = (0 : Matrix (Fin 4) (Fin 4) ℤ) * U := by rw [h]
    rw [Matrix.add_mul, Matrix.zero_mul, Matrix.mul_assoc, hUTU, Matrix.mul_smul,
      Matrix.mul_one] at h'
    rw [eq_neg_iff_add_eq_zero]
    exact h'
  · intro h
    have h' : ((4 : ℤ) • E) * U.transpose
        = (-(p * (Lam (dvec κ x ρ)).transpose * U)) * U.transpose := by rw [h]
    rw [Matrix.smul_mul, Matrix.neg_mul, Matrix.mul_assoc, hUUT, Matrix.mul_smul,
      Matrix.mul_one] at h'
    ext i j
    have hij := congrFun (congrFun h' i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply] at hij
    simp only [Matrix.add_apply, Matrix.zero_apply]
    omega

end HadamardBFormalCore
