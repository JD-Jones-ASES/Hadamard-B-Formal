/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import HadamardBFormal.Border

/-!
# Lemma 3 (compression) and Theorem A, sufficiency direction

`NOTE-B` §1.1.  This file carries the one genuinely new sum-reindexing block of
the development and the theorem it unlocks.

## The bijection

Every coset reindexing used below is an instance of a **single** bijection
argument, `sum_fiber_equiv`: a bijection of `G` that carries the fiber of `κ`
over `c` onto the fiber over `c'` transports the corresponding sums.  The three
cases of `NOTE-B`'s Lemma 3,

```
Σ_{h ∈ κ⁻¹(c)} x(h − g)   = σ(c − κg)
Σ_{h ∈ κ⁻¹(c)} x(ρ − g − h) = σ(κρ − κg − c)
Σ_{h ∈ κ⁻¹(c)} x(g + h − ρ) = σ(κg + c − κρ)
```

are then `Equiv.subRight`, `Equiv.subLeft` and `Equiv.subRight` again (at the
shifted point `ρ − g`), with **no second bijection argument**.

## The results

* `cosetSum_sub_right`, `cosetSum_sub_left`, `cosetSum_add_left` — the three
  transport lemmas;
* `gsBlock_fiber_sum` — the sixteen-case sign bookkeeping, stated across two
  unrelated index types because the two arrays live over `G` and over `Ḡ`;
* `compression` — **Lemma 3**: `Σ_{κh = c} C[(I,g),(J,h)] = Ĉ[(I,κg),(J,c)]`;
* `paf_cosetSum`, `sumPaf_cosetSum`, `chat_gram` — the **Σ̄ law**, the note's
  corollary to Lemma 3: `Ĉ Ĉᵀ = I₄ ⊗ Σ̄` with `Σ̄(ē) = Σ_{t ∈ κ⁻¹(ē)} Σ PAF(t)`;
* `theoremA_sufficiency` — **Theorem A, sufficiency, at general `κ`**.

Theorem A's sufficiency direction lives here rather than in `Border.lean`
because it consumes Lemma 3; `Border.lean` carries the shared mechanics and
cannot import this file.

Note that **surjectivity of `κ` is not used** in the sufficiency direction: only
the constancy of the fiber size enters, through `rowStrip_mul_transpose`.  (It is
the necessity direction that needs every `t` in a coset to be realised.)
-/

namespace HadamardBFormal

open scoped BigOperators Matrix

/-! ### The one bijection argument -/

/-- **The master coset bijection.**  If `e` is a bijection of `G` carrying the
fiber of `κ` over `c` onto the fiber over `c'`, then summing `F ∘ e` over the
first fiber is the coset sum of `F` at `c'`.

Everything in `NOTE-B`'s Lemma 3 is an instance of this lemma; the bijection
argument is run **once**. -/
theorem sum_fiber_equiv {G Gbar : Type*} [Fintype G] [DecidableEq Gbar] (κ : G → Gbar)
    (F : G → ℤ) (e : G ≃ G) (c c' : Gbar) (he : ∀ h : G, κ h = c ↔ κ (e h) = c') :
    (∑ h with κ h = c, F (e h)) = cosetSum κ F c' := by
  rw [cosetSum]
  refine Finset.sum_equiv e (fun h => ?_) (fun h _ => rfl)
  simpa using he h

/-- **Lemma 3, first case.**  `Σ_{κh = c} x(h − g) = σ(c − κg)`. -/
theorem cosetSum_sub_right {G Gbar : Type*} [Fintype G] [AddCommGroup G] [AddCommGroup Gbar]
    [DecidableEq Gbar] (κ : G →+ Gbar) (x : G → ℤ) (g : G) (c : Gbar) :
    (∑ h with κ h = c, x (h - g)) = cosetSum κ x (c - κ g) :=
  sum_fiber_equiv κ x (Equiv.subRight g) c (c - κ g) fun h => by
    change κ h = c ↔ κ (h - g) = c - κ g
    rw [map_sub, sub_left_inj]

/-- **Lemma 3, reflected case.**  `Σ_{κh = c} x(g − h) = σ(κg − c)`.  Taking
`g := ρ − g₀` gives the note's `Σ_{κh = c} x(ρ − g₀ − h) = σ(κρ − κg₀ − c)`. -/
theorem cosetSum_sub_left {G Gbar : Type*} [Fintype G] [AddCommGroup G] [AddCommGroup Gbar]
    [DecidableEq Gbar] (κ : G →+ Gbar) (x : G → ℤ) (g : G) (c : Gbar) :
    (∑ h with κ h = c, x (g - h)) = cosetSum κ x (κ g - c) :=
  sum_fiber_equiv κ x (Equiv.subLeft g) c (κ g - c) fun h => by
    change κ h = c ↔ κ (g - h) = κ g - c
    rw [map_sub, sub_right_inj]

/-- Translation transport: `Σ_{κh = c} x(g + h) = σ(κg + c)`.  Used for the
periodic autocorrelation, not for Lemma 3 itself. -/
theorem cosetSum_add_left {G Gbar : Type*} [Fintype G] [AddCommGroup G] [AddCommGroup Gbar]
    [DecidableEq Gbar] (κ : G →+ Gbar) (x : G → ℤ) (g : G) (c : Gbar) :
    (∑ h with κ h = c, x (g + h)) = cosetSum κ x (κ g + c) :=
  sum_fiber_equiv κ x (Equiv.addLeft g) c (κ g + c) fun h => by
    change κ h = c ↔ κ (g + h) = κ g + c
    rw [map_add, add_right_inj]

/-! ### The three block shapes -/

/-- A plain developed block compresses to the developed block of the coset sums. -/
theorem dev_fiber_sum {G Gbar : Type*} [Fintype G] [AddCommGroup G] [AddCommGroup Gbar]
    [DecidableEq Gbar] (κ : G →+ Gbar) (x : G → ℤ) (g : G) (c : Gbar) :
    (∑ h with κ h = c, dev x g h) = dev (cosetSum κ x) (κ g) c := by
  simp only [dev_apply]
  exact cosetSum_sub_right κ x g c

/-- A reversed developed block compresses to the reversed block over the quotient,
with the reflection shift `κ ρ`. -/
theorem dev_fiber_sum_rev {G Gbar : Type*} [Fintype G] [AddCommGroup G] [AddCommGroup Gbar]
    [DecidableEq Gbar] (κ : G →+ Gbar) (x : G → ℤ) (ρ g : G) (c : Gbar) :
    (∑ h with κ h = c, dev x g (reflect ρ h)) =
      dev (cosetSum κ x) (κ g) (reflect (κ ρ) c) := by
  have hL : ∀ h : G, dev x g (reflect ρ h) = x (ρ - g - h) := by
    intro h
    simp only [dev_apply, reflect_apply]
    congr 1
    abel
  simp only [hL]
  rw [cosetSum_sub_left κ x (ρ - g) c]
  simp only [dev_apply, reflect_apply, map_sub]
  congr 1
  abel

/-- A reversed *transposed* developed block compresses likewise. -/
theorem dev_fiber_sum_revT {G Gbar : Type*} [Fintype G] [AddCommGroup G] [AddCommGroup Gbar]
    [DecidableEq Gbar] (κ : G →+ Gbar) (x : G → ℤ) (ρ g : G) (c : Gbar) :
    (∑ h with κ h = c, dev x (reflect ρ h) g) =
      dev (cosetSum κ x) (reflect (κ ρ) c) (κ g) := by
  have hL : ∀ h : G, dev x (reflect ρ h) g = x (h - (ρ - g)) := by
    intro h
    simp only [dev_apply, reflect_apply]
    congr 1
    abel
  simp only [hL]
  rw [cosetSum_sub_right κ x (ρ - g) c]
  simp only [dev_apply, reflect_apply, map_sub]
  congr 1
  abel

/-! ### Lemma 3 -/

/-- **The block-level bookkeeping of Lemma 3.**  If each of the three shapes in
which a block of the Goethals--Seidel table can occur compresses to the
corresponding shape over the quotient, then so does every one of the sixteen
positions — signs included, since the block signs are untouched by summation.

Stated across two unrelated index types because the two arrays live over `G` and
over `Ḡ`. -/
theorem gsBlock_fiber_sum {G Gb : Type*} [Fintype G] [DecidableEq Gb] (κ : G → Gb)
    (r : Equiv.Perm G) (X : Fin 4 → Matrix G G ℤ) (r' : Equiv.Perm Gb)
    (Y : Fin 4 → Matrix Gb Gb ℤ) (g : G) (c : Gb)
    (hplain : ∀ q, (∑ h with κ h = c, X q g h) = Y q (κ g) c)
    (hrev : ∀ q, (∑ h with κ h = c, X q g (r h)) = Y q (κ g) (r' c))
    (hrevT : ∀ q, (∑ h with κ h = c, X q (r h) g) = Y q (r' c) (κ g))
    (I J : Fin 4) :
    (∑ h with κ h = c, gsBlock r X I J g h) = gsBlock r' Y I J (κ g) c := by
  fin_cases I <;> fin_cases J <;>
    simp only [gsBlock, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.neg_apply, revCols_apply, Matrix.transpose_apply,
      Finset.sum_neg_distrib, hplain, hrev, hrevT]

/-- **Lemma 3 (compression)** (`NOTE-B` §1.1).  Summing a row of the core over a
`K`-coset depends on the row index `g` only through `κ g`, and the resulting
`4i × 4i` matrix is `Ĉ = GS(σ₀,…,σ₃; κρ)`, the Goethals--Seidel array of the
coset sums over the quotient group. -/
theorem compression {G Gbar : Type*} [Fintype G] [AddCommGroup G] [AddCommGroup Gbar]
    [DecidableEq Gbar] (κ : G →+ Gbar) (x : Fin 4 → G → ℤ) (ρ : G) (I J : Fin 4) (g : G)
    (c : Gbar) :
    (∑ h with κ h = c, core x ρ (I, g) (J, h)) = chat κ x ρ (I, κ g) (J, c) :=
  gsBlock_fiber_sum κ (reflect ρ) (fun q => dev (x q)) (reflect (κ ρ))
    (fun q => dev (cosetSum κ (x q))) g c
    (fun q => dev_fiber_sum κ (x q) g c)
    (fun q => dev_fiber_sum_rev κ (x q) ρ g c)
    (fun q => dev_fiber_sum_revT κ (x q) ρ g c) I J

/-! ### The Σ̄ law -/

/-- The compressed aggregate profile `Σ̄(ē) = Σ_{t ∈ κ⁻¹(ē)} Σ PAF(t)`. -/
def sigmaBar {G Gbar : Type*} [Fintype G] [AddCommGroup G] [DecidableEq Gbar] (κ : G → Gbar)
    (x : Fin 4 → G → ℤ) (e : Gbar) : ℤ :=
  ∑ t with κ t = e, sumPaf x t

/-- **Compression of the periodic autocorrelation** (the Đoković--Kotsireas
device).  The PAF of a coset-sum sequence is the fiber sum of the PAF. -/
theorem paf_cosetSum {G Gbar : Type*} [Fintype G] [AddCommGroup G] [Fintype Gbar]
    [AddCommGroup Gbar] [DecidableEq Gbar] (κ : G →+ Gbar) (x : G → ℤ) (e : Gbar) :
    paf (cosetSum κ x) e = ∑ t with κ t = e, paf x t := by
  have step1 : (∑ t with κ t = e, paf x t) = ∑ u : G, x u * cosetSum κ x (κ u + e) := by
    simp only [paf]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.mul_sum]
    exact congrArg (fun z => x u * z) (cosetSum_add_left κ x u e)
  have step2 : (∑ u : G, x u * cosetSum κ x (κ u + e)) = paf (cosetSum κ x) e := by
    rw [← Finset.sum_fiberwise Finset.univ κ fun u : G => x u * cosetSum κ x (κ u + e), paf]
    refine Finset.sum_congr rfl fun ubar _ => ?_
    calc (∑ u with κ u = ubar, x u * cosetSum κ x (κ u + e))
        = ∑ u with κ u = ubar, x u * cosetSum κ x (ubar + e) := by
          refine Finset.sum_congr rfl fun u hu => ?_
          rw [(Finset.mem_filter.mp hu).2]
      _ = (∑ u with κ u = ubar, x u) * cosetSum κ x (ubar + e) := by rw [Finset.sum_mul]
      _ = cosetSum κ x ubar * cosetSum κ x (ubar + e) := rfl
  exact (step1.trans step2).symm

/-- The aggregate form: `Σ PAF` of the coset sums is `Σ̄`. -/
theorem sumPaf_cosetSum {G Gbar : Type*} [Fintype G] [AddCommGroup G] [Fintype Gbar]
    [AddCommGroup Gbar] [DecidableEq Gbar] (κ : G →+ Gbar) (x : Fin 4 → G → ℤ) (e : Gbar) :
    sumPaf (fun q => cosetSum κ (x q)) e = sigmaBar κ x e := by
  have hswap : sigmaBar κ x e = ∑ q : Fin 4, ∑ t with κ t = e, paf (x q) t := by
    simp only [sigmaBar, sumPaf]
    exact Finset.sum_comm
  rw [hswap, sumPaf]
  exact Finset.sum_congr rfl fun q _ => paf_cosetSum κ (x q) e

/-- **The Σ̄ law** (`NOTE-B` §1.1, the corollary to Lemma 3).
`Ĉ Ĉᵀ = I₄ ⊗ Σ̄` with `Σ̄(ē) = Σ_{t ∈ κ⁻¹(ē)} Σ PAF(t)`. -/
theorem chat_gram {G Gbar : Type*} [Fintype G] [AddCommGroup G] [Fintype Gbar]
    [AddCommGroup Gbar] [DecidableEq Gbar] (κ : G →+ Gbar) (x : Fin 4 → G → ℤ) (ρ : G)
    (a b : Fin 4) (e e' : Gbar) :
    (chat κ x ρ * (chat κ x ρ).transpose) (a, e) (b, e') =
      if a = b then sigmaBar κ x (e - e') else 0 := by
  rw [chat, core_gram, sumPaf_cosetSum]

/-! ### The two off-diagonal strips -/

/-- **The top-right computation** (`NOTE-B` §1.1).  By Lemma 3,
`(P̃ Cᵀ)[r,(I,g)] = (P Ĉᵀ)[r,(I,κg)]`. -/
theorem rowStrip_mul_core_transpose {G Gbar : Type*} [Fintype G] [AddCommGroup G]
    [Fintype Gbar] [AddCommGroup Gbar] [DecidableEq Gbar] {s : ℕ} (κ : G →+ Gbar)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ) (x : Fin 4 → G → ℤ) (ρ : G)
    (r : Fin (4 * s)) (I : Fin 4) (g : G) :
    (rowStrip κ P * (core x ρ).transpose) r (I, g)
      = (P * (chat κ x ρ).transpose) r (I, κ g) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowStrip_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← Finset.sum_fiberwise Finset.univ κ fun h : G => P r (J, κ h) * core x ρ (I, g) (J, h)]
  refine Finset.sum_congr rfl fun c _ => ?_
  calc (∑ h with κ h = c, P r (J, κ h) * core x ρ (I, g) (J, h))
      = ∑ h with κ h = c, P r (J, c) * core x ρ (I, g) (J, h) := by
        refine Finset.sum_congr rfl fun h hh => ?_
        rw [(Finset.mem_filter.mp hh).2]
    _ = P r (J, c) * ∑ h with κ h = c, core x ρ (I, g) (J, h) := by rw [Finset.mul_sum]
    _ = P r (J, c) * chat κ x ρ (I, κ g) (J, c) := by rw [compression]

/-- The column strip reads `E Qᵀ` at the image index; this is a definitional
identity. -/
theorem mul_colStrip_transpose_apply {G Gbar : Type*} {s : ℕ} (κ : G → Gbar)
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ) (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (r : Fin (4 * s)) (z : Fin 4 × G) :
    (E * (colStrip κ Q).transpose) r z = (E * Q.transpose) r (z.1, κ z.2) :=
  rfl

/-! ### `M(0) = 4s` is forced -/

/-- `M(0) = 4s` is automatic (`NOTE-B` §1.1): the rows of `Q` are `±1` vectors of
length `4s`, so the diagonal of `Q Qᵀ` is `4s`. -/
theorem M_zero_of_H1 {Gbar : Type*} [AddCommGroup Gbar] {s : ℕ}
    {Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ} (hQ : ∀ z c, IsSign (Q z c)) {M : Gbar → ℤ}
    (h1 : H1 Q M) : M 0 = 4 * (s : ℤ) := by
  have h : (∑ c, Q ((0 : Fin 4), (0 : Gbar)) c * Q ((0 : Fin 4), (0 : Gbar)) c) = M 0 := by
    simpa using h1 (0, 0) (0, 0)
  have hone : ∀ c : Fin (4 * s),
      Q ((0 : Fin 4), (0 : Gbar)) c * Q ((0 : Fin 4), (0 : Gbar)) c = 1 := by
    intro c
    rcases hQ ((0 : Fin 4), (0 : Gbar)) c with hc | hc <;> rw [hc] <;> norm_num
  rw [← h, Finset.sum_congr rfl fun c _ => hone c, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  ring

/-! ### Theorem A, sufficiency -/

/-- **Theorem A, sufficiency direction, at general `κ`** (`NOTE-B` §1.1).

Let `κ : G →+ Ḡ` have all fibers of size `w`, let `E`, `P`, `Q` and the seed
quadruple `x` be sign valued, and let `M : Ḡ → ℤ` satisfy

* **(H1)** `Q Qᵀ = I₄ ⊗ M`,
* **(H2)** `Σ PAF(t) = −M(κ t)` for `t ≠ 0`,
* **(H3)** `E Eᵀ + w · P Pᵀ = N · I`, and
* **(H4)** `E Qᵀ + P Ĉᵀ = 0`, with `Ĉ` the compressed core.

Then the bordered array `H = [[E, P̃],[Q̃, C]]` is a Hadamard matrix of order
`N = 4(|G| + s)`.

The three blocks of the note's display enter as: (H3) through
`rowStrip_mul_transpose` (top-left), (H1)+(H2) through `core_gram` and
`M_zero_of_H1` (bottom-right), and (H4) through **Lemma 3**
(`rowStrip_mul_core_transpose`, top-right), the bottom-left being the transpose
of the top-right.

Surjectivity of `κ` is **not** needed here; it is the necessity direction that
uses it. -/
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
  have hcardG : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨(0 : G)⟩
  have hcard : (Fintype.card (Fin (4 * s) ⊕ (Fin 4 × G)) : ℤ)
      = 4 * ((Fintype.card G : ℤ) + s) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have hM0 : M 0 = 4 * (s : ℤ) := M_zero_of_H1 hQ h1
  -- (H3) is the top-left block, once the strip Gram is unfolded.
  have hTL : E * E.transpose + rowStrip κ P * (rowStrip κ P).transpose
      = (4 * ((Fintype.card G : ℤ) + s)) • 1 := by
    rw [rowStrip_mul_transpose κ hw]
    exact h3
  -- (H4) is the top-right block, once Lemma 3 is applied.
  have hTR : E * (colStrip κ Q).transpose + rowStrip κ P * (core x ρ).transpose = 0 := by
    ext r z
    obtain ⟨I, g⟩ := z
    have h4' := congrFun (congrFun h4 r) ((I, κ g) : Fin 4 × Gbar)
    rw [Matrix.add_apply, Matrix.zero_apply] at h4'
    rw [Matrix.add_apply, Matrix.zero_apply, mul_colStrip_transpose_apply,
      rowStrip_mul_core_transpose]
    exact h4'
  have hBL : colStrip κ Q * E.transpose + core x ρ * (rowStrip κ P).transpose = 0 := by
    have h := congrArg Matrix.transpose hTR
    simpa [Matrix.transpose_add, Matrix.transpose_mul] using h
  -- (H1) + (H2) are the bottom-right block.
  have hBR : colStrip κ Q * (colStrip κ Q).transpose + core x ρ * (core x ρ).transpose
      = (4 * ((Fintype.card G : ℤ) + s)) • 1 := by
    ext z z'
    obtain ⟨I, g⟩ := z
    obtain ⟨J, h⟩ := z'
    have hQQ : (Q * Q.transpose) (I, κ g) (J, κ h) = if I = J then M (κ g - κ h) else 0 :=
      h1 (I, κ g) (J, κ h)
    rw [Matrix.add_apply, colStrip_mul_transpose_apply, hQQ, core_gram, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply]
    by_cases hIJ : I = J
    · subst hIJ
      rw [if_pos rfl, if_pos rfl]
      by_cases hgh : g = h
      · subst hgh
        simp only [sub_self]
        rw [hM0, sumPaf_zero hx, if_pos trivial]
        ring
      · rw [h2 (g - h) (sub_ne_zero_of_ne hgh), map_sub, if_neg (by simp [hgh])]
        ring
    · rw [if_neg hIJ, if_neg hIJ, if_neg (by simp [hIJ]), add_zero, mul_zero]
  refine Matrix.IsHadamard.of_mul_conjTranspose
    (fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
      (border_isSign κ E P Q x ρ hE hP hQ hx i j)) ?_ ?_
  · rw [Matrix.conjTranspose_eq_transpose_of_trivial, hcard, border_gram_iff]
    exact ⟨hTL, hTR, hBL, hBR⟩
  · rw [isRegular_iff_ne_zero, hcard]
    omega

end HadamardBFormal
