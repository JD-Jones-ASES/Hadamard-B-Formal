/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import HadamardBFormal.TheoremD

/-!
# (D-a′): the degenerate branch is the `i = 1` construction, written twice

`NOTE-B` §1.5, clause (D-a′).  `theoremD_tables` splits the Gram dichotomy of (D-a)
into two branches; `TheoremD.lean` follows the genuine one, `M(1) = −4`.  This file
follows the other one, `M(1) = +4` — the branch in which `M = 4J₂`, both tiers of the
profile coalesce, and the claim is that the border **is** an `i = 1` border in `i = 2`
bookkeeping.

The spine, in the note's order:

* `theoremD_tables_degenerate` (`TheoremD.lean`) — `Q` pairs up **equal**;
* `chat_rowDiff` / `chat_rowDiff_one` and `chat_colSum` — the compressed-block
  identities of (D-a′), the differenced and summed tables of `Ĉ` read across rows and
  down columns, both instances of `gsBlock_eval`;
* `deltaSqSum_degenerate` — the degenerate-branch Parseval `Σ_q δ_q² = N`.  The
  invariants swap: the genuine branch has `Σ_q δ_q² = 4` and `Σ_q r_q² = N`
  (`deltaSqSum_eq_four`, `D5`), the degenerate branch has them the other way round;
* `theoremD_rowTable_degenerate` — hence `Λ(d)Λ(d)ᵀ = N·I₄` is nonsingular, and (H4)
  kills the column **differences** of `P`: `P` pairs up **equal** too.  Exact mirror of
  (D-c), where it is `Λ(r)` that is inverted and the column *sums* that die;
* `border_degenerate_eq` — the strips then carry no coset dependence, so `H = H₁`
  **entry for entry**, on the nose, as matrices over the same index type;
* `degenerate_H1_iff`, `degenerate_H3_iff`, `degenerate_H4_iff` — the termwise
  transport of the hypotheses, in both directions;
* `theoremD_degenerate_collapse` and `theoremD_degenerate_converse` — the two halves
  of the note's bijection.

`K` is invisible in the degenerate branch's data: the collapsed tables `collapseRow P`
and `collapseCol Q` see only `P[r][(J,0)]` and `Q[(I,0)]`, and every hypothesis and the
assembled matrix are recovered from them.
-/

namespace HadamardBFormalCore

open scoped BigOperators Matrix

/-! ### `ε² = 1`, and the mass of the twisted vector -/

/-- `ε = ±1`, so `ε² = 1`. -/
theorem eps_mul_self {G : Type*} [AddCommGroup G] (κ : G →+ ZMod 2) (ρ : G) :
    eps κ ρ * eps κ ρ = 1 := by
  rcases zmod2_cases (κ ρ) with h | h
  · rw [eps_of_zero h]; norm_num
  · rw [eps_of_one h]; norm_num

/-- `Σ_q d_q² = Σ_q δ_q²`: the `ε` in `d = (δ₀, εδ₁, εδ₂, εδ₃)` does not change the mass. -/
theorem dvec_mul_self_sum {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (x : Fin 4 → G → ℤ) (ρ : G) :
    (∑ q, dvec κ x ρ q * dvec κ x ρ q) = ∑ q, delta κ (x q) ^ 2 := by
  have hkey : ∀ a : ℤ, eps κ ρ * a * (eps κ ρ * a) = a ^ 2 := by
    intro a
    calc eps κ ρ * a * (eps κ ρ * a) = eps κ ρ * eps κ ρ * (a * a) := by ring
      _ = a ^ 2 := by rw [eps_mul_self]; ring
  have h0 : dvec κ x ρ 0 = delta κ (x 0) := rfl
  have h1 : dvec κ x ρ 1 = eps κ ρ * delta κ (x 1) := rfl
  have h2 : dvec κ x ρ 2 = eps κ ρ * delta κ (x 2) := rfl
  have h3 : dvec κ x ρ 3 = eps κ ρ * delta κ (x 3) := rfl
  rw [Fin.sum_univ_four, Fin.sum_univ_four, h0, h1, h2, h3, hkey, hkey, hkey]
  ring

/-! ### The degenerate-branch Parseval step -/

/-- The `ψ`-mass of the group vanishes when the two fibers of `κ` have the same size. -/
theorem psi2_sum_eq_zero {G : Type*} [Fintype G] [AddCommGroup G] {w : ℕ} (κ : G →+ ZMod 2)
    (hw : ∀ c : ZMod 2, (Finset.univ.filter fun g : G => κ g = c).card = w) :
    (∑ g : G, psi2 κ g) = 0 := by
  have h := sum_comp_of_card_fiber_eq (⇑κ) hw fun c : ZMod 2 => if c = 0 then (1 : ℤ) else -1
  rw [zmod2_sum,
    show ((if (0 : ZMod 2) = 0 then (1 : ℤ) else -1) + (if (1 : ZMod 2) = 0 then (1 : ℤ) else -1))
      = 0 from by decide, mul_zero] at h
  simpa only [psi2_apply] using h

/-- **`Σ_q δ_q² = N`** (`NOTE-B` §1.5, (D-a′), third item).

In the degenerate branch `M = 4J₂` the profile is the constant `−4` off the origin, so
the `ψ`-twisted mass is `4n` at the origin and `−4·Σ_{t≠0} ψ(t) = +4` away from it: the
note's `Σ̄(0) − Σ̄(1) = (4n − 4(w−1)) − (−4w) = 4n + 4`.

Unlike `deltaSqSum_eq_four` this **does** need the two fibers to have the same size:
`Σ_g ψ(g) = 0` is where the index enters.  The two invariants are exactly swapped
between the branches — here `Σ_q δ_q² = N` and `Σ_q r_q² = 4`, there the reverse. -/
theorem deltaSqSum_degenerate {G : Type*} [Fintype G] [AddCommGroup G] {w : ℕ}
    (κ : G →+ ZMod 2)
    (hw : ∀ c : ZMod 2, (Finset.univ.filter fun g : G => κ g = c).card = w)
    (x : Fin 4 → G → ℤ) (hx : ∀ q g, IsSign (x q g)) {M : ZMod 2 → ℤ}
    (hM : ∀ c : ZMod 2, M c = 4) (h2 : H2 x κ M) :
    (∑ q, delta κ (x q) ^ 2) = 4 * ((Fintype.card G : ℤ) + 1) := by
  classical
  have hdecomp : ∀ t : G, psi2 κ t * sumPaf x t
      = -4 * psi2 κ t + (4 * (Fintype.card G : ℤ) + 4) * (if t = 0 then (1 : ℤ) else 0) := by
    intro t
    by_cases ht : t = 0
    · subst ht
      rw [sumPaf_zero hx, if_pos rfl, AddChar.map_zero_eq_one]
      ring
    · rw [h2 t ht, if_neg ht, hM (κ t)]
      ring
  have hsumd : (∑ t : G, (if t = 0 then (1 : ℤ) else 0)) = 1 := by simp
  calc (∑ q, delta κ (x q) ^ 2)
      = ∑ q, (∑ g, psi2 κ g * x q g) ^ 2 :=
        Finset.sum_congr rfl fun q _ => by rw [delta_eq]
    _ = ∑ t : G, sumPaf (fun q g => psi2 κ g * x q g) t :=
        (sum_sumPaf_eq_sq fun q g => psi2 κ g * x q g).symm
    _ = ∑ t : G, psi2 κ t * sumPaf x t :=
        Finset.sum_congr rfl fun t _ => sumPaf_twist (psi2 κ) (psi2_sq κ) x t
    _ = 4 * ((Fintype.card G : ℤ) + 1) := by
        rw [Finset.sum_congr rfl fun t (_ : t ∈ Finset.univ) => hdecomp t,
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsumd,
          psi2_sum_eq_zero κ hw]
        ring

/-! ### The compressed-block identities of (D-a′)

`NOTE-B` §1.5 displays two identities of `ℤ[σ]` at every block position: the (D-d)
table *differenced across the two row classes*, and the same table *summed down the two
column classes*.  Both are `gsBlock_eval` run against a different functional.  Over
`ZMod 2` every block of `Ĉ` is symmetric, which is why the row-differenced table is the
same `Λ(d)` that `chat_colDiff` reads off the columns. -/

/-- Differencing the two rows of a plain compressed block at column class `0` gives `δ`. -/
theorem chatShape_rowDiff_plain {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) :
    dev (cosetSum κ y) 0 0 - dev (cosetSum κ y) 1 0 = delta κ y := by
  simp only [dev_apply]
  rw [show ((0 : ZMod 2) - 0) = 0 from by decide, show ((0 : ZMod 2) - 1) = 1 from by decide,
    delta]

/-- The same for a reversed block: `εδ`. -/
theorem chatShape_rowDiff_rev {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) (ρ : G) :
    revCols (reflect (κ ρ)) (dev (cosetSum κ y)) 0 0
      - revCols (reflect (κ ρ)) (dev (cosetSum κ y)) 1 0 = eps κ ρ * delta κ y := by
  have e1 : ∀ k : ZMod 2, k - 0 - 0 = k := by decide
  have e2 : ∀ k : ZMod 2, k - 0 - 1 = k - 1 := by decide
  simp only [revCols_apply, reflect_apply, dev_apply]
  rw [e1 (κ ρ), e2 (κ ρ)]
  exact cosetSum_shift_diff κ y ρ

/-- The same for a transposed reversed block: `εδ`. -/
theorem chatShape_rowDiff_revT {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) (ρ : G) :
    revCols (reflect (κ ρ)) ((dev (cosetSum κ y)).transpose) 0 0
      - revCols (reflect (κ ρ)) ((dev (cosetSum κ y)).transpose) 1 0 = eps κ ρ * delta κ y := by
  have e1 : ∀ k : ZMod 2, (0 : ZMod 2) - (k - 0) = k := by decide
  have e2 : ∀ k : ZMod 2, (1 : ZMod 2) - (k - 0) = k - 1 := by decide
  simp only [revCols_apply, Matrix.transpose_apply, reflect_apply, dev_apply]
  rw [e1 (κ ρ), e2 (κ ρ)]
  exact cosetSum_shift_diff κ y ρ

/-- The three shapes again at column class `1`, where every value is negated. -/
theorem chatShape_rowDiffOne_plain {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) :
    dev (cosetSum κ y) 0 1 - dev (cosetSum κ y) 1 1 = -delta κ y := by
  simp only [dev_apply]
  rw [show ((1 : ZMod 2) - 0) = 1 from by decide, show ((1 : ZMod 2) - 1) = 0 from by decide,
    delta]
  ring

theorem chatShape_rowDiffOne_rev {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) (ρ : G) :
    revCols (reflect (κ ρ)) (dev (cosetSum κ y)) 0 1
      - revCols (reflect (κ ρ)) (dev (cosetSum κ y)) 1 1 = -(eps κ ρ * delta κ y) := by
  have e1 : ∀ k : ZMod 2, k - 1 - 0 = k - 1 := by decide
  have e2 : ∀ k : ZMod 2, k - 1 - 1 = k := by decide
  have h := cosetSum_shift_diff κ y ρ
  simp only [revCols_apply, reflect_apply, dev_apply]
  rw [e1 (κ ρ), e2 (κ ρ)]
  linarith

theorem chatShape_rowDiffOne_revT {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) (ρ : G) :
    revCols (reflect (κ ρ)) ((dev (cosetSum κ y)).transpose) 0 1
      - revCols (reflect (κ ρ)) ((dev (cosetSum κ y)).transpose) 1 1
      = -(eps κ ρ * delta κ y) := by
  have e1 : ∀ k : ZMod 2, (0 : ZMod 2) - (k - 1) = k - 1 := by decide
  have e2 : ∀ k : ZMod 2, (1 : ZMod 2) - (k - 1) = k := by decide
  have h := cosetSum_shift_diff κ y ρ
  simp only [revCols_apply, Matrix.transpose_apply, reflect_apply, dev_apply]
  rw [e1 (κ ρ), e2 (κ ρ)]
  linarith

/-- **The row-differenced table** (`NOTE-B` §1.5, first display of (D-a′)):
`Ĉ[(I,0),(J,0)] − Ĉ[(I,1),(J,0)] = Λ(d)[I][J]`. -/
theorem chat_rowDiff {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (x : Fin 4 → G → ℤ) (ρ : G) (I J : Fin 4) :
    chat κ x ρ (I, 0) (J, 0) - chat κ x ρ (I, 1) (J, 0) = Lam (dvec κ x ρ) I J := by
  refine gsBlock_eval (reflect (κ ρ)) (fun q => dev (cosetSum κ (x q)))
    (fun B => B 0 0 - B 1 0) (fun A => by simp only [Matrix.neg_apply]; ring) (dvec κ x ρ)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ I J
  · exact chatShape_rowDiff_plain κ (x 0)
  · exact chatShape_rowDiff_rev κ (x 1) ρ
  · exact chatShape_rowDiff_rev κ (x 2) ρ
  · exact chatShape_rowDiff_rev κ (x 3) ρ
  · exact chatShape_rowDiff_revT κ (x 1) ρ
  · exact chatShape_rowDiff_revT κ (x 2) ρ
  · exact chatShape_rowDiff_revT κ (x 3) ρ

/-- The row-differenced table at the second column class: `−Λ(d)`. -/
theorem chat_rowDiff_one {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (x : Fin 4 → G → ℤ) (ρ : G) (I J : Fin 4) :
    chat κ x ρ (I, 0) (J, 1) - chat κ x ρ (I, 1) (J, 1) = -Lam (dvec κ x ρ) I J := by
  have h : (fun B : Matrix (ZMod 2) (ZMod 2) ℤ => B 0 1 - B 1 1)
      (gsBlock (reflect (κ ρ)) (fun q => dev (cosetSum κ (x q))) I J)
      = Lam (fun q => -dvec κ x ρ q) I J := by
    refine gsBlock_eval (reflect (κ ρ)) (fun q => dev (cosetSum κ (x q)))
      (fun B => B 0 1 - B 1 1) (fun A => by simp only [Matrix.neg_apply]; ring)
      (fun q => -dvec κ x ρ q) ?_ ?_ ?_ ?_ ?_ ?_ ?_ I J
    · exact chatShape_rowDiffOne_plain κ (x 0)
    · exact chatShape_rowDiffOne_rev κ (x 1) ρ
    · exact chatShape_rowDiffOne_rev κ (x 2) ρ
    · exact chatShape_rowDiffOne_rev κ (x 3) ρ
    · exact chatShape_rowDiffOne_revT κ (x 1) ρ
    · exact chatShape_rowDiffOne_revT κ (x 2) ρ
    · exact chatShape_rowDiffOne_revT κ (x 3) ρ
  rw [Lam_neg] at h
  exact h

/-- Summing a plain compressed block down its two columns gives the row sum. -/
theorem chatShape_colSum_plain {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) (c : ZMod 2) :
    dev (cosetSum κ y) c 0 + dev (cosetSum κ y) c 1 = ∑ g, y g := by
  have hne : ∀ k : ZMod 2, (0 : ZMod 2) - k ≠ 1 - k := by decide
  simp only [dev_apply]
  exact cosetSum_pair_add κ y (hne c)

/-- The same for a reversed block. -/
theorem chatShape_colSum_rev {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) (ρ : G) (c : ZMod 2) :
    revCols (reflect (κ ρ)) (dev (cosetSum κ y)) c 0
      + revCols (reflect (κ ρ)) (dev (cosetSum κ y)) c 1 = ∑ g, y g := by
  have hne : ∀ k c : ZMod 2, k - 0 - c ≠ k - 1 - c := by decide
  simp only [revCols_apply, reflect_apply, dev_apply]
  exact cosetSum_pair_add κ y (hne (κ ρ) c)

/-- The same for a transposed reversed block. -/
theorem chatShape_colSum_revT {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (y : G → ℤ) (ρ : G) (c : ZMod 2) :
    revCols (reflect (κ ρ)) ((dev (cosetSum κ y)).transpose) c 0
      + revCols (reflect (κ ρ)) ((dev (cosetSum κ y)).transpose) c 1 = ∑ g, y g := by
  have hne : ∀ k c : ZMod 2, c - (k - 0) ≠ c - (k - 1) := by decide
  simp only [revCols_apply, Matrix.transpose_apply, reflect_apply, dev_apply]
  exact cosetSum_pair_add κ y (hne (κ ρ) c)

/-- **The column-summed table** (`NOTE-B` §1.5, second display of (D-a′), read down the
columns): `Ĉ[(I,c),(J,0)] + Ĉ[(I,c),(J,1)] = Λ(r)[I][J]`, whatever the row class.  No `ε`
enters — the companion of `chat_rowSum`. -/
theorem chat_colSum {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (x : Fin 4 → G → ℤ) (ρ : G) (I J : Fin 4) (c : ZMod 2) :
    chat κ x ρ (I, c) (J, 0) + chat κ x ρ (I, c) (J, 1) = Lam (rvec x) I J := by
  refine gsBlock_eval (reflect (κ ρ)) (fun q => dev (cosetSum κ (x q)))
    (fun B => B c 0 + B c 1) (fun A => by simp only [Matrix.neg_apply]; ring) (rvec x)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ I J
  · exact chatShape_colSum_plain κ (x 0) c
  · exact chatShape_colSum_rev κ (x 1) ρ c
  · exact chatShape_colSum_rev κ (x 2) ρ c
  · exact chatShape_colSum_rev κ (x 3) ρ c
  · exact chatShape_colSum_revT κ (x 1) ρ c
  · exact chatShape_colSum_revT κ (x 2) ρ c
  · exact chatShape_colSum_revT κ (x 3) ρ c

/-! ### `P` pairs up equal -/

/-- **Theorem D, clause (D-a′), third item** (`NOTE-B` §1.5).

Once the column table has paired up **equal**, `E Qᵀ` has `col(2I+1) = col(2I)`, so by
(H4) `P Ĉᵀ` must too; the row-differenced table turns that into `Λ(d)·b_r = 0` with
`b_{rJ} = P[r][(J,0)] − P[r][(J,1)]`.  The degenerate Parseval step gives
`Σ_q d_q² = N ≠ 0`, so `Λ(d)` is nonsingular and `b_r = 0`.

Exact mirror of (D-c): there it is `Λ(r)` that is inverted and the column *sums* that
die.  Neither `w ≥ 2`, nor (H3), nor the sign-valuedness of `E` and `P` is used — only
the seeds have to be sign valued, for `Σ PAF(0) = 4n`. -/
theorem theoremD_rowTable_degenerate {G : Type*} [Fintype G] [AddCommGroup G] {w : ℕ}
    (κ : G →+ ZMod 2)
    (hw : ∀ c : ZMod 2, (Finset.univ.filter fun g : G => κ g = c).card = w)
    (E : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ) (P : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ)
    (Q : Matrix (Fin 4 × ZMod 2) (Fin (4 * 1)) ℤ) (x : Fin 4 → G → ℤ) (ρ : G)
    (hx : ∀ q g, IsSign (x q g)) {M : ZMod 2 → ℤ} (hM : ∀ c : ZMod 2, M c = 4)
    (h2 : H2 x κ M) (h4 : H4 (s := 1) E P Q (chat κ x ρ))
    (hQpair : ∀ I : Fin 4, Q (I, 1) = Q (I, 0)) :
    ∀ r J : Fin 4, P r (J, 1) = P r (J, 0) := by
  have hQe : ∀ (I : Fin 4) (e : Fin (4 * 1)),
      Q (I, (1 : ZMod 2)) e = Q (I, (0 : ZMod 2)) e := by
    intro I e
    rw [hQpair I]
  -- (H4), entrywise.
  have h4' : ∀ (r I : Fin 4) (c : ZMod 2),
      (∑ e : Fin (4 * 1), E r e * Q (I, c) e)
        + ∑ J : Fin 4, ∑ b : ZMod 2, P r (J, b) * chat κ x ρ (I, c) (J, b) = 0 := by
    intro r I c
    have h := congrFun (congrFun h4 r) ((I, c) : Fin 4 × ZMod 2)
    simpa only [Matrix.add_apply, Matrix.zero_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_prod_type] using h
  -- Differencing the two row classes kills the corner and leaves `Λ(d)·b_r = 0`.
  have hLamAnn : ∀ r I : Fin 4,
      (∑ J : Fin 4, (P r (J, 0) - P r (J, 1)) * Lam (dvec κ x ρ) I J) = 0 := by
    intro r I
    have h0 := h4' r I 0
    have h1 := h4' r I 1
    have hEcancel : (∑ e : Fin (4 * 1), E r e * Q (I, (0 : ZMod 2)) e)
        - (∑ e : Fin (4 * 1), E r e * Q (I, (1 : ZMod 2)) e) = 0 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [hQe I e]
      ring
    have hCJ : ∀ J : Fin 4,
        (∑ b : ZMod 2, P r (J, b) * chat κ x ρ (I, 0) (J, b))
          - (∑ b : ZMod 2, P r (J, b) * chat κ x ρ (I, 1) (J, b))
          = (P r (J, 0) - P r (J, 1)) * Lam (dvec κ x ρ) I J := by
      intro J
      have e0 : chat κ x ρ (I, 0) (J, 0)
          = chat κ x ρ (I, 1) (J, 0) + Lam (dvec κ x ρ) I J := by
        have := chat_rowDiff κ x ρ I J
        linarith
      have e1 : chat κ x ρ (I, 0) (J, 1)
          = chat κ x ρ (I, 1) (J, 1) - Lam (dvec κ x ρ) I J := by
        have := chat_rowDiff_one κ x ρ I J
        linarith
      rw [zmod2_sum, zmod2_sum, e0, e1]
      ring
    have hzero : (∑ J : Fin 4, ∑ b : ZMod 2, P r (J, b) * chat κ x ρ (I, 0) (J, b))
        - (∑ J : Fin 4, ∑ b : ZMod 2, P r (J, b) * chat κ x ρ (I, 1) (J, b)) = 0 := by
      linarith
    rw [← hzero, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun J _ => (hCJ J).symm
  -- `Σ_q d_q² = N ≠ 0`, so `Λ(d)` is nonsingular.
  have hN : (∑ q, dvec κ x ρ q * dvec κ x ρ q) = 4 * ((Fintype.card G : ℤ) + 1) := by
    rw [dvec_mul_self_sum, deltaSqSum_degenerate κ hw x hx hM h2]
  have hNpos : (0 : ℤ) < 4 * ((Fintype.card G : ℤ) + 1) := by
    have hc : (0 : ℤ) ≤ (Fintype.card G : ℤ) := Int.natCast_nonneg _
    linarith
  have hLT : ∀ J0 J : Fin 4, (∑ I : Fin 4, Lam (dvec κ x ρ) I J0 * Lam (dvec κ x ρ) I J)
      = if J0 = J then 4 * ((Fintype.card G : ℤ) + 1) else 0 := by
    intro J0 J
    have h := congrFun (congrFun (Lam_transpose_mul (dvec κ x ρ)) J0) J
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at h
    simp only [Matrix.transpose_apply] at h
    rw [hN] at h
    rw [h]
    by_cases hJ : J0 = J
    · rw [if_pos hJ, if_pos hJ, mul_one]
    · rw [if_neg hJ, if_neg hJ, mul_zero]
  have hPdiff : ∀ r J : Fin 4, P r (J, 0) - P r (J, 1) = 0 := by
    intro r J0
    have hkill : 4 * ((Fintype.card G : ℤ) + 1) * (P r (J0, 0) - P r (J0, 1)) = 0 := by
      calc 4 * ((Fintype.card G : ℤ) + 1) * (P r (J0, 0) - P r (J0, 1))
          = ∑ J : Fin 4, (if J0 = J then 4 * ((Fintype.card G : ℤ) + 1) else 0)
              * (P r (J, 0) - P r (J, 1)) := by simp
        _ = ∑ J : Fin 4, ∑ I : Fin 4,
              Lam (dvec κ x ρ) I J0 * ((P r (J, 0) - P r (J, 1)) * Lam (dvec κ x ρ) I J) := by
            refine Finset.sum_congr rfl fun J _ => ?_
            rw [← hLT J0 J, Finset.sum_mul]
            exact Finset.sum_congr rfl fun I _ => by ring
        _ = ∑ I : Fin 4, ∑ J : Fin 4,
              Lam (dvec κ x ρ) I J0 * ((P r (J, 0) - P r (J, 1)) * Lam (dvec κ x ρ) I J) :=
            Finset.sum_comm
        _ = ∑ I : Fin 4, Lam (dvec κ x ρ) I J0
              * ∑ J : Fin 4, (P r (J, 0) - P r (J, 1)) * Lam (dvec κ x ρ) I J :=
            Finset.sum_congr rfl fun I _ => (Finset.mul_sum _ _ _).symm
        _ = 0 := Finset.sum_eq_zero fun I _ => by rw [hLamAnn r I, mul_zero]
    rcases mul_eq_zero.mp hkill with h' | h'
    · exact absurd h' (by linarith)
    · exact h'
  intro r J
  have h := hPdiff r J
  linarith

/-! ### The collapsed tables, and the assembled matrix -/

/-- The collapsed row table `P₁[r][J] = P[r][(J,0)]`, read over a trivial quotient. -/
def collapseRow {Gbar' : Type*} (P : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ) :
    Matrix (Fin (4 * 1)) (Fin 4 × Gbar') ℤ :=
  fun r z => P r (z.1, 0)

/-- The collapsed column table `Q₁[I] = Q[(I,0)]`, read over a trivial quotient. -/
def collapseCol {Gbar' : Type*} (Q : Matrix (Fin 4 × ZMod 2) (Fin (4 * 1)) ℤ) :
    Matrix (Fin 4 × Gbar') (Fin (4 * 1)) ℤ :=
  fun z c => Q (z.1, 0) c

/-- A sum over a subsingleton is its value at `0`. -/
theorem sum_subsingleton_eq {Gbar' : Type*} [Fintype Gbar'] [Zero Gbar'] [Subsingleton Gbar']
    (f : Gbar' → ℤ) : (∑ c : Gbar', f c) = f 0 :=
  Finset.sum_eq_single (0 : Gbar') (fun b _ hb => absurd (Subsingleton.elim b 0) hb)
    fun h => absurd (Finset.mem_univ _) h

/-- **The assembled matrices are equal, entry for entry** (`NOTE-B` §1.5, (D-a′), fourth
item).  Once both border tables pair up equal, the two strips lose all coset dependence:
`P̃[r,(J,h)] = P₁[r][J]` and `Q̃[(I,g),c] = Q₁[I][c]`, with no dependence on `h` or `g`.
The cores are literally the same matrix.  So `H = H₁` on the nose — the degenerate branch
does not move the assembled matrix, and `K` is invisible in its data. -/
theorem border_degenerate_eq {G Gbar' : Type*} [AddCommGroup G] [AddCommGroup Gbar']
    (κ : G →+ ZMod 2) (κ₀ : G →+ Gbar')
    (E : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ) (P : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ)
    (Q : Matrix (Fin 4 × ZMod 2) (Fin (4 * 1)) ℤ) (x : Fin 4 → G → ℤ) (ρ : G)
    (hPpair : ∀ r J : Fin 4, P r (J, 1) = P r (J, 0))
    (hQpair : ∀ I : Fin 4, Q (I, 1) = Q (I, 0)) :
    border κ E P Q x ρ = border κ₀ E (collapseRow P) (collapseCol Q) x ρ := by
  ext i j
  match i, j with
  | Sum.inl _, Sum.inl _ => rfl
  | Sum.inl r, Sum.inr z =>
    change P r (z.1, κ z.2) = P r (z.1, 0)
    rcases zmod2_cases (κ z.2) with h | h
    · rw [h]
    · rw [h, hPpair r z.1]
  | Sum.inr z, Sum.inl c =>
    change Q (z.1, κ z.2) c = Q (z.1, 0) c
    rcases zmod2_cases (κ z.2) with h | h
    · rw [h]
    · rw [h, hQpair z.1]
  | Sum.inr _, Sum.inr _ => rfl

/-! ### The hypotheses transport termwise -/

/-- **(H1) transports.**  With the column table paired up equal, (H1) at index two with
the constant table `M = 4J₂` is (H1) at index one with `M₁ = (4)`. -/
theorem degenerate_H1_iff {Gbar' : Type*} [AddCommGroup Gbar']
    (Q : Matrix (Fin 4 × ZMod 2) (Fin (4 * 1)) ℤ)
    (hQpair : ∀ I : Fin 4, Q (I, 1) = Q (I, 0)) :
    H1 (s := 1) Q (fun _ : ZMod 2 => 4) ↔
      H1 (s := 1) (collapseCol (Gbar' := Gbar') Q) (fun _ : Gbar' => 4) := by
  have hQe : ∀ (I : Fin 4) (c : ZMod 2) (e : Fin (4 * 1)), Q (I, c) e = Q (I, 0) e := by
    intro I c e
    rcases zmod2_cases c with h | h
    · rw [h]
    · rw [h, hQpair I]
  have hred : ∀ (I J : Fin 4) (c c' : ZMod 2),
      (∑ e : Fin (4 * 1), Q (I, c) e * Q (J, c') e)
        = ∑ e : Fin (4 * 1), Q (I, (0 : ZMod 2)) e * Q (J, (0 : ZMod 2)) e :=
    fun I J c c' => Finset.sum_congr rfl fun e _ => by rw [hQe I c e, hQe J c' e]
  constructor
  · rintro h ⟨I, c⟩ ⟨J, c'⟩
    change (∑ e : Fin (4 * 1), Q (I, (0 : ZMod 2)) e * Q (J, (0 : ZMod 2)) e)
      = if I = J then (4 : ℤ) else 0
    exact h (I, 0) (J, 0)
  · rintro h ⟨I, c⟩ ⟨J, c'⟩
    change (∑ e : Fin (4 * 1), Q (I, c) e * Q (J, c') e) = if I = J then (4 : ℤ) else 0
    rw [hred I J c c']
    exact h (I, 0) (J, 0)

/-- The doubled row table doubles the Gram: `P Pᵀ = 2 · P₁ P₁ᵀ`. -/
theorem collapseRow_gram {Gbar' : Type*} [Fintype Gbar'] [Zero Gbar'] [Subsingleton Gbar']
    (P : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ)
    (hPpair : ∀ r J : Fin 4, P r (J, 1) = P r (J, 0)) :
    P * P.transpose
      = (2 : ℤ) • (collapseRow (Gbar' := Gbar') P
          * (collapseRow (Gbar' := Gbar') P).transpose) := by
  ext r t
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [zmod2_sum, sum_subsingleton_eq]
  simp only [collapseRow, hPpair r J, hPpair t J]
  ring

/-- **(H3) transports.**  The doubling turns fiber size `w` into `n = 2w`. -/
theorem degenerate_H3_iff {G Gbar' : Type*} [Fintype G] [AddCommGroup G]
    [AddCommGroup Gbar'] [Fintype Gbar'] [DecidableEq Gbar'] [Subsingleton Gbar'] {w : ℕ}
    (κ : G →+ ZMod 2)
    (hw : ∀ c : ZMod 2, (Finset.univ.filter fun g : G => κ g = c).card = w)
    (E : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ) (P : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ)
    (hPpair : ∀ r J : Fin 4, P r (J, 1) = P r (J, 0)) (N : ℤ) :
    H3 (s := 1) E P (w : ℤ) N ↔
      H3 (s := 1) E (collapseRow (Gbar' := Gbar') P) (Fintype.card G : ℤ) N := by
  have hn : (Fintype.card G : ℤ) = 2 * (w : ℤ) := by
    have h := sum_comp_of_card_fiber_eq (⇑κ) hw fun _ => (1 : ℤ)
    rw [zmod2_sum] at h
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
    rw [h]
    ring
  simp only [H3]
  rw [collapseRow_gram (Gbar' := Gbar') P hPpair, smul_smul,
    show (w : ℤ) * 2 = (Fintype.card G : ℤ) from by rw [hn]; ring]

/-- The compressed core over a trivial quotient is the constant table `Λ(r)`: every
coset sum is the row sum, so `Ĉ[(I,c),(J,c′)] = Λ(r)[I][J]`. -/
theorem chat_subsingleton {G Gbar' : Type*} [Fintype G] [AddCommGroup G]
    [AddCommGroup Gbar'] [DecidableEq Gbar'] [Subsingleton Gbar'] (κ₀ : G →+ Gbar')
    (x : Fin 4 → G → ℤ) (ρ : G) (I J : Fin 4) (c c' : Gbar') :
    chat κ₀ x ρ (I, c) (J, c') = Lam (rvec x) I J := by
  refine gsBlock_eval (reflect (κ₀ ρ)) (fun q => dev (cosetSum κ₀ (x q)))
    (fun B => B c c') (fun _ => rfl) (rvec x) ?_ ?_ ?_ ?_ ?_ ?_ ?_ I J
  · exact cosetSum_subsingleton κ₀ (x 0) _
  · exact cosetSum_subsingleton κ₀ (x 1) _
  · exact cosetSum_subsingleton κ₀ (x 2) _
  · exact cosetSum_subsingleton κ₀ (x 3) _
  · exact cosetSum_subsingleton κ₀ (x 1) _
  · exact cosetSum_subsingleton κ₀ (x 2) _
  · exact cosetSum_subsingleton κ₀ (x 3) _

/-- **(H4) transports.**  With both tables paired up equal, the `4 × 8` condition (H4) at
index two and the `4 × 4` condition `E Q₁ᵀ + P₁ Λ(r)ᵀ = 0` at index one are the same
equation — read at either row class, since the two rows of a block of `Ĉ` have equal
column sums.  This is the note's "(H4) read at `c = 0` becomes the `i = 1` border
equation, with the row-sum vector `r` where the genuine branch has `d`". -/
theorem degenerate_H4_iff {G Gbar' : Type*} [Fintype G] [AddCommGroup G]
    [AddCommGroup Gbar'] [Fintype Gbar'] [DecidableEq Gbar'] [Subsingleton Gbar']
    (κ : G →+ ZMod 2) (κ₀ : G →+ Gbar')
    (E : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ) (P : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ)
    (Q : Matrix (Fin 4 × ZMod 2) (Fin (4 * 1)) ℤ) (x : Fin 4 → G → ℤ) (ρ : G)
    (hPpair : ∀ r J : Fin 4, P r (J, 1) = P r (J, 0))
    (hQpair : ∀ I : Fin 4, Q (I, 1) = Q (I, 0)) :
    H4 (s := 1) E P Q (chat κ x ρ) ↔
      H4 (s := 1) E (collapseRow (Gbar' := Gbar') P) (collapseCol Q) (chat κ₀ x ρ) := by
  have hQe : ∀ (I : Fin 4) (c : ZMod 2) (e : Fin (4 * 1)), Q (I, c) e = Q (I, 0) e := by
    intro I c e
    rcases zmod2_cases c with h | h
    · rw [h]
    · rw [h, hQpair I]
  have hL : ∀ (r I : Fin 4) (c : ZMod 2),
      (E * Q.transpose + P * (chat κ x ρ).transpose) r (I, c)
        = (∑ e : Fin (4 * 1), E r e * Q (I, (0 : ZMod 2)) e)
          + ∑ J : Fin 4, P r (J, 0) * Lam (rvec x) I J := by
    intro r I c
    have e1 : (∑ e : Fin (4 * 1), E r e * Q (I, c) e)
        = ∑ e : Fin (4 * 1), E r e * Q (I, (0 : ZMod 2)) e :=
      Finset.sum_congr rfl fun e _ => by rw [hQe I c e]
    have e2 : (∑ J : Fin 4, ∑ b : ZMod 2, P r (J, b) * chat κ x ρ (I, c) (J, b))
        = ∑ J : Fin 4, P r (J, 0) * Lam (rvec x) I J := by
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [zmod2_sum, hPpair r J, ← chat_colSum κ x ρ I J c]
      ring
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
    rw [Fintype.sum_prod_type, e1, e2]
  have hR : ∀ (r I : Fin 4) (c : Gbar'),
      (E * (collapseCol (Gbar' := Gbar') Q).transpose
          + collapseRow (Gbar' := Gbar') P * (chat κ₀ x ρ).transpose) r (I, c)
        = (∑ e : Fin (4 * 1), E r e * Q (I, (0 : ZMod 2)) e)
          + ∑ J : Fin 4, P r (J, 0) * Lam (rvec x) I J := by
    intro r I c
    have e2 : (∑ J : Fin 4, ∑ b : Gbar',
          collapseRow (Gbar' := Gbar') P r (J, b) * chat κ₀ x ρ (I, c) (J, b))
        = ∑ J : Fin 4, P r (J, 0) * Lam (rvec x) I J := by
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [sum_subsingleton_eq]
      simp only [collapseRow, chat_subsingleton]
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
    rw [Fintype.sum_prod_type, e2]
    rfl
  simp only [H4]
  constructor
  · intro h
    have h' : ∀ r I : Fin 4, (∑ e : Fin (4 * 1), E r e * Q (I, (0 : ZMod 2)) e)
        + ∑ J : Fin 4, P r (J, 0) * Lam (rvec x) I J = 0 := by
      intro r I
      rw [← hL r I 0]
      exact congrFun (congrFun h r) ((I, (0 : ZMod 2)) : Fin 4 × ZMod 2)
    ext r z
    obtain ⟨I, c⟩ := z
    rw [Matrix.zero_apply, hR r I c]
    exact h' r I
  · intro h
    have h' : ∀ r I : Fin 4, (∑ e : Fin (4 * 1), E r e * Q (I, (0 : ZMod 2)) e)
        + ∑ J : Fin 4, P r (J, 0) * Lam (rvec x) I J = 0 := by
      intro r I
      rw [← hR r I 0]
      exact congrFun (congrFun h r) ((I, (0 : Gbar')) : Fin 4 × Gbar')
    ext r z
    obtain ⟨I, c⟩ := z
    rw [Matrix.zero_apply, hL r I c]
    exact h' r I

/-! ### (D-a′) itself -/

/-- **Theorem D, clause (D-a′)** (`NOTE-B` §1.5): *the degenerate branch collapses, and
this is exactly what that means.*

In the branch `M(1) = +4` — where `M = 4J₂`, both tiers of the profile coalesce and
(H2) reads `Σ PAF(t) = −4` for **every** `t ≠ 0` — the border data **is** `i = 1` data
written in `i = 2` bookkeeping:

1. `Q` pairs up **equal**, `Q[(I,1)] = Q[(I,0)]`;
2. `P` pairs up **equal**, `P[r][(J,1)] = P[r][(J,0)]`;
3. the assembled matrix is the `i = 1` assembly, **entry for entry**: `H = H₁`;
4. and the hypotheses transport termwise — (H1) with `M₁ = (4)`, (H2) the `i = 1`
   profile, (H3) at fiber size `n` rather than `w`, and (H4) the `i = 1` border
   equation `E Q₁ᵀ + P₁ Λ(r)ᵀ = 0`, with the row-sum vector `r` where the genuine
   branch has the twisted vector `d`.

The trivial quotient is carried as any hom `κ₀ : G →+ Ḡ′` into a subsingleton, exactly
as in `borderedGS_subsingleton`; the collapsed tables read only `P[r][(J,0)]` and
`Q[(I,0)]`, so `K` never appears in them.  `theoremD_degenerate_converse` is the other
half of the note's bijection. -/
theorem theoremD_degenerate_collapse {G Gbar' : Type*} [Fintype G] [AddCommGroup G]
    [AddCommGroup Gbar'] [Fintype Gbar'] [DecidableEq Gbar'] [Subsingleton Gbar'] {w : ℕ}
    (κ : G →+ ZMod 2) (κ₀ : G →+ Gbar')
    (hw : ∀ c : ZMod 2, (Finset.univ.filter fun g : G => κ g = c).card = w)
    (E : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ) (P : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ)
    (Q : Matrix (Fin 4 × ZMod 2) (Fin (4 * 1)) ℤ) (x : Fin 4 → G → ℤ) (ρ : G)
    (hQ : ∀ z c, IsSign (Q z c)) (hx : ∀ q g, IsSign (x q g))
    (M : ZMod 2 → ℤ) (hM1 : M 1 = 4) (h1 : H1 (s := 1) Q M) (h2 : H2 x κ M)
    (h3 : H3 (s := 1) E P (w : ℤ) (4 * ((Fintype.card G : ℤ) + 1)))
    (h4 : H4 (s := 1) E P Q (chat κ x ρ)) :
    (∀ I : Fin 4, Q (I, 1) = Q (I, 0)) ∧
      (∀ r J : Fin 4, P r (J, 1) = P r (J, 0)) ∧
      border κ E P Q x ρ = border κ₀ E (collapseRow P) (collapseCol Q) x ρ ∧
      H1 (s := 1) (collapseCol (Gbar' := Gbar') Q) (fun _ : Gbar' => 4) ∧
      H2 x κ₀ (fun _ : Gbar' => 4) ∧
      H3 (s := 1) E (collapseRow (Gbar' := Gbar') P) (Fintype.card G : ℤ)
        (4 * ((Fintype.card G : ℤ) + 1)) ∧
      H4 (s := 1) E (collapseRow (Gbar' := Gbar') P) (collapseCol Q) (chat κ₀ x ρ) := by
  obtain ⟨hM0, -, -, -⟩ := theoremD_gramContraction Q hQ M h1
  obtain ⟨hQpair, -⟩ := theoremD_tables_degenerate Q hQ M h1 hM1
  have hMc : ∀ c : ZMod 2, M c = 4 := by
    intro c
    rcases zmod2_cases c with h | h
    · rw [h]; exact hM0
    · rw [h]; exact hM1
  have hPpair : ∀ r J : Fin 4, P r (J, 1) = P r (J, 0) :=
    theoremD_rowTable_degenerate κ hw E P Q x ρ hx hMc h2 h4 hQpair
  have h1' : H1 (s := 1) Q (fun _ : ZMod 2 => (4 : ℤ)) := by
    intro a b
    rw [h1 a b, hMc]
  have h2' : H2 x κ (fun _ : ZMod 2 => (4 : ℤ)) := by
    intro t ht
    rw [h2 t ht, hMc]
  exact ⟨hQpair, hPpair, border_degenerate_eq κ κ₀ E P Q x ρ hPpair hQpair,
    (degenerate_H1_iff Q hQpair).mp h1', fun t ht => h2' t ht,
    (degenerate_H3_iff κ hw E P hPpair _).mp h3,
    (degenerate_H4_iff κ κ₀ E P Q x ρ hPpair hQpair).mp h4⟩

/-- **The converse of (D-a′)** (`NOTE-B` §1.5): *conversely, doubling any `i = 1` border
gives (H1)–(H4) with `M = 4J₂`.*

Doubling is encoded by the two pair-equality hypotheses: tables `P`, `Q` over `ZMod 2`
that repeat each block along the two classes are precisely the doublings of their own
collapsed tables.  Given the `i = 1` hypotheses on those collapsed tables, every `i = 2`
hypothesis follows, with the degenerate Gram table `M = 4J₂` — and the assembled matrix
is again the same one.

With `theoremD_degenerate_collapse` this is the note's bijection: doubling is a bijection
between the `(s,i) = (1,1)` borders and the degenerate-branch `(s,i) = (1,2)` borders for
the same seeds, and it does not move the assembled matrix. -/
theorem theoremD_degenerate_converse {G Gbar' : Type*} [Fintype G] [AddCommGroup G]
    [AddCommGroup Gbar'] [Fintype Gbar'] [DecidableEq Gbar'] [Subsingleton Gbar'] {w : ℕ}
    (κ : G →+ ZMod 2) (κ₀ : G →+ Gbar')
    (hw : ∀ c : ZMod 2, (Finset.univ.filter fun g : G => κ g = c).card = w)
    (E : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ) (P : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ)
    (Q : Matrix (Fin 4 × ZMod 2) (Fin (4 * 1)) ℤ) (x : Fin 4 → G → ℤ) (ρ : G)
    (hPpair : ∀ r J : Fin 4, P r (J, 1) = P r (J, 0))
    (hQpair : ∀ I : Fin 4, Q (I, 1) = Q (I, 0))
    (h1 : H1 (s := 1) (collapseCol (Gbar' := Gbar') Q) (fun _ : Gbar' => 4))
    (h2 : H2 x κ₀ (fun _ : Gbar' => 4))
    (h3 : H3 (s := 1) E (collapseRow (Gbar' := Gbar') P) (Fintype.card G : ℤ)
      (4 * ((Fintype.card G : ℤ) + 1)))
    (h4 : H4 (s := 1) E (collapseRow (Gbar' := Gbar') P) (collapseCol Q) (chat κ₀ x ρ)) :
    H1 (s := 1) Q (fun _ : ZMod 2 => 4) ∧ H2 x κ (fun _ : ZMod 2 => 4) ∧
      H3 (s := 1) E P (w : ℤ) (4 * ((Fintype.card G : ℤ) + 1)) ∧
      H4 (s := 1) E P Q (chat κ x ρ) ∧
      border κ E P Q x ρ = border κ₀ E (collapseRow P) (collapseCol Q) x ρ :=
  ⟨(degenerate_H1_iff Q hQpair).mpr h1, fun t ht => h2 t ht,
    (degenerate_H3_iff κ hw E P hPpair _).mpr h3,
    (degenerate_H4_iff κ κ₀ E P Q x ρ hPpair hQpair).mpr h4,
    border_degenerate_eq κ κ₀ E P Q x ρ hPpair hQpair⟩

end HadamardBFormalCore
