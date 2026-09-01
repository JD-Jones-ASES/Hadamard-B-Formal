/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import HadamardBFormal.Compression

/-!
# Theorem A: the exact characterisation

`NOTE-B` §1.1.  `Compression.lean` proves the sufficiency direction; this file
supplies the converse and packages the two into the **iff** of Theorem A.

## The necessity argument

`border_gram_iff` (`Border.lean`) already reads `H Hᵀ = N · I` off as four block
equations, so the converse is a matter of reading the same four equations
backwards.

* the **top-left** equation is (H3) verbatim, once `rowStrip_mul_transpose`
  replaces `P̃ P̃ᵀ` by `w · P Pᵀ`;
* the **top-right** equation is (H4) evaluated at `(r, (J, κ g))`; here
  surjectivity of `κ` is what supplies a `g` for each quotient index;
* the **bottom-left** equation is the transpose of the top-right and carries no
  further information;
* the **bottom-right** equation carries both (H1) and (H2).  The Gram table is
  *constructed* as `M e := (Q Qᵀ)[(0,e),(0,0)]`.  For (H2) no surjectivity is
  needed: the bottom-right equation at `((0,t),(0,0))` reads `M (κ t) + Σ PAF(t) = 0`
  directly.  For (H1) with `I ≠ J` surjectivity picks representatives `g, h`;
  for `I = J` the equation at `((I,g),(I,h))` and the equation at
  `((0,g−h),(0,0))` have the *same* right-hand side, so no section of `κ` and no
  well-definedness argument is needed.

The note's sentence "the left side depends on `g,g'` only through their cosets
and the right side only through `g−g'`, and every `t` in the coset is realised"
is exactly `gram_sameSuperblock_ne` used twice.

## The results

* `border_isHadamard_iff_gram` — the bridge between `Matrix.IsHadamard` and the
  primitive Gram equation `H Hᵀ = 4(n+s) · I`;
* `theoremA_necessity` — the converse direction;
* `theoremA` — **Theorem A**, the iff;
* `M_symm` — symmetry of the Gram table, a *consequence* of (H1) rather than a
  hypothesis (`NOTE-B` §1.1 states `M` symmetric; it need not be assumed).
-/

namespace HadamardBFormalCore

open scoped BigOperators Matrix

/-! ### The order of the bordered array -/

/-- The bordered array has order `N = 4(n + s)`. -/
theorem border_card {G : Type*} [Fintype G] (s : ℕ) :
    (Fintype.card (Fin (4 * s) ⊕ (Fin 4 × G)) : ℤ) = 4 * ((Fintype.card G : ℤ) + s) := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Fintype.card_fin]
  push_cast
  ring

/-- For sign-valued data, Hadamardness of the bordered array is exactly the Gram
equation `H Hᵀ = 4(n + s) · I`.  This is the bridge between the two forms in
which Theorem A can be stated. -/
theorem border_isHadamard_iff_gram {G Gbar : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup Gbar] {s : ℕ} (κ : G →+ Gbar)
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G)
    (hE : ∀ r c, IsSign (E r c)) (hP : ∀ r z, IsSign (P r z))
    (hQ : ∀ z c, IsSign (Q z c)) (hx : ∀ q g, IsSign (x q g)) :
    Matrix.IsHadamard (border κ E P Q x ρ) ↔
      border κ E P Q x ρ * (border κ E P Q x ρ).transpose
        = (4 * ((Fintype.card G : ℤ) + s)) • 1 := by
  have hcardG : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨(0 : G)⟩
  constructor
  · intro hH
    have h := hH.mul_conjTranspose
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, border_card (G := G) s] at h
  · intro h
    refine Matrix.IsHadamard.of_mul_conjTranspose
      (fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
        (border_isSign κ E P Q x ρ hE hP hQ hx i j)) ?_ ?_
    · rw [Matrix.conjTranspose_eq_transpose_of_trivial, border_card (G := G) s]
      exact h
    · rw [isRegular_iff_ne_zero, border_card (G := G) s]
      omega

/-! ### The bottom-right block, read backwards -/

/-- The bottom-right block of `H Hᵀ`, entrywise: `Q̃ Q̃ᵀ` reads `Q Qᵀ` at the images
and `C Cᵀ` is the aggregate profile (Lemma 2). -/
theorem colStrip_add_core_gram_apply {G Gbar : Type*} [AddCommGroup G] [Fintype G]
    [AddCommGroup Gbar] {s : ℕ} (κ : G →+ Gbar)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ) (x : Fin 4 → G → ℤ) (ρ : G)
    (I J : Fin 4) (g h : G) :
    (colStrip κ Q * (colStrip κ Q).transpose + core x ρ * (core x ρ).transpose) (I, g) (J, h)
      = (Q * Q.transpose) (I, κ g) (J, κ h) + (if I = J then sumPaf x (g - h) else 0) := by
  rw [Matrix.add_apply, colStrip_mul_transpose_apply, core_gram]

/-- The dot product of two rows of `Q` is an entry of `Q Qᵀ`. -/
theorem sum_mul_eq_mul_transpose_apply {ι κ : Type*} [Fintype κ] (Q : Matrix ι κ ℤ) (a b : ι) :
    (∑ c, Q a c * Q b c) = (Q * Q.transpose) a b :=
  rfl

/-- **`Q Qᵀ` has no cross-superblock entries.**  This is the note's
"`I ≠ I' ⟹ Q Qᵀ` has zero cross-superblock blocks". -/
theorem gram_offSuperblock {G Gbar : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup Gbar] {s : ℕ} {κ : G →+ Gbar}
    {Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ} {x : Fin 4 → G → ℤ} {ρ : G} {N : ℤ}
    (hBR : colStrip κ Q * (colStrip κ Q).transpose + core x ρ * (core x ρ).transpose = N • 1)
    {I J : Fin 4} (hIJ : I ≠ J) (g h : G) :
    (Q * Q.transpose) (I, κ g) (J, κ h) = 0 := by
  have h := congrFun (congrFun hBR (I, g)) (J, h)
  rw [colStrip_add_core_gram_apply, if_neg hIJ, add_zero, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, if_neg (by simp [hIJ]), mul_zero] at h
  exact h

/-- **The off-diagonal of a superblock of `Q Qᵀ` is `−Σ PAF`.**  This is the note's
"`I = I'`, `g ≠ g' ⟹ (Q Qᵀ)[iI+κg, iI+κg'] = −Σ PAF(g−g')`". -/
theorem gram_sameSuperblock_ne {G Gbar : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup Gbar] {s : ℕ} {κ : G →+ Gbar}
    {Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ} {x : Fin 4 → G → ℤ} {ρ : G} {N : ℤ}
    (hBR : colStrip κ Q * (colStrip κ Q).transpose + core x ρ * (core x ρ).transpose = N • 1)
    (I : Fin 4) {g h : G} (hgh : g ≠ h) :
    (Q * Q.transpose) (I, κ g) (I, κ h) = -sumPaf x (g - h) := by
  have h := congrFun (congrFun hBR (I, g)) (I, h)
  rw [colStrip_add_core_gram_apply, if_pos rfl, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, if_neg (by simp [hgh]), mul_zero] at h
  omega

/-- **The diagonal of `Q Qᵀ` is `N − 4n`.**  This is the note's
"`I = I'`, `g = g' ⟹ (Q Qᵀ)[iI+c,iI+c] = N − 4n = 4s`, automatic". -/
theorem gram_sameSuperblock_self {G Gbar : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup Gbar] {s : ℕ} {κ : G →+ Gbar}
    {Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ} {x : Fin 4 → G → ℤ} {ρ : G} {N : ℤ}
    (hBR : colStrip κ Q * (colStrip κ Q).transpose + core x ρ * (core x ρ).transpose = N • 1)
    (I : Fin 4) (g : G) :
    (Q * Q.transpose) (I, κ g) (I, κ g) = N - sumPaf x 0 := by
  have h := congrFun (congrFun hBR (I, g)) (I, g)
  rw [colStrip_add_core_gram_apply, if_pos rfl, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, if_pos rfl, mul_one, sub_self] at h
  omega

/-! ### Symmetry of the Gram table -/

/-- **`M` is symmetric.**  `NOTE-B` §1.1 asks for a symmetric `Ḡ`-invariant `M`;
symmetry is in fact a consequence of (H1), so Theorem A's right-hand side does not
have to carry it. -/
theorem M_symm {Gbar : Type*} [AddCommGroup Gbar] {s : ℕ}
    {Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ} {M : Gbar → ℤ} (h1 : H1 Q M) (e : Gbar) :
    M (-e) = M e := by
  have h₁ : (∑ c, Q ((0 : Fin 4), (0 : Gbar)) c * Q ((0 : Fin 4), e) c) = M (-e) := by
    simpa using h1 (0, 0) (0, e)
  have h₂ : (∑ c, Q ((0 : Fin 4), e) c * Q ((0 : Fin 4), (0 : Gbar)) c) = M e := by
    simpa using h1 (0, e) (0, 0)
  rw [← h₁, ← h₂]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

/-! ### Theorem A, necessity -/

/-- **Theorem A, necessity direction** (`NOTE-B` §1.1).  If the bordered array has
Gram `N · I` with `N = 4(n + s)`, then (H1)--(H4) hold, with the Gram table
constructed as `M e = (Q Qᵀ)[(0,e),(0,0)]`.

Surjectivity of `κ` is used exactly twice: to realise each quotient index of the
row table in (H4), and to realise each pair of quotient indices in the
cross-superblock clause of (H1).  It is **not** needed for (H2), nor for the
`I = J` clause of (H1). -/
theorem theoremA_necessity {G Gbar : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup Gbar] [Fintype Gbar] [DecidableEq Gbar] {s w : ℕ} (κ : G →+ Gbar)
    (hκ : Function.Surjective κ)
    (hw : ∀ c : Gbar, (Finset.univ.filter fun g : G => κ g = c).card = w)
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G)
    (hgram : border κ E P Q x ρ * (border κ E P Q x ρ).transpose
      = (4 * ((Fintype.card G : ℤ) + s)) • 1) :
    (∃ M : Gbar → ℤ, H1 Q M ∧ H2 x κ M)
      ∧ H3 E P (w : ℤ) (4 * ((Fintype.card G : ℤ) + s))
      ∧ H4 E P Q (chat κ x ρ) := by
  rw [border_gram_iff] at hgram
  obtain ⟨hTL, hTR, -, hBR⟩ := hgram
  refine ⟨⟨fun e => (Q * Q.transpose) ((0 : Fin 4), e) ((0 : Fin 4), (0 : Gbar)), ?_, ?_⟩,
    ?_, ?_⟩
  · -- (H1)
    rintro ⟨I, c⟩ ⟨J, c'⟩
    obtain ⟨g, rfl⟩ := hκ c
    obtain ⟨h, rfl⟩ := hκ c'
    change (∑ cc, Q (I, κ g) cc * Q (J, κ h) cc)
      = if I = J then (Q * Q.transpose) ((0 : Fin 4), κ g - κ h) ((0 : Fin 4), (0 : Gbar))
        else 0
    rw [sum_mul_eq_mul_transpose_apply]
    split_ifs with hIJ
    · subst hIJ
      by_cases hgh : g = h
      · subst hgh
        have h0 := gram_sameSuperblock_self hBR (0 : Fin 4) (0 : G)
        rw [map_zero] at h0
        rw [gram_sameSuperblock_self hBR I g, sub_self, h0]
      · have h0 := gram_sameSuperblock_ne hBR (0 : Fin 4) (sub_ne_zero_of_ne hgh)
        rw [map_sub, map_zero, sub_zero] at h0
        rw [gram_sameSuperblock_ne hBR I hgh, h0]
    · exact gram_offSuperblock hBR hIJ g h
  · -- (H2)
    intro t ht
    change sumPaf x t = -(Q * Q.transpose) ((0 : Fin 4), κ t) ((0 : Fin 4), (0 : Gbar))
    have h0 := gram_sameSuperblock_ne hBR (0 : Fin 4) (x := x) (ρ := ρ) ht
    rw [map_zero, sub_zero] at h0
    rw [h0, neg_neg]
  · -- (H3)
    have h := hTL
    rw [rowStrip_mul_transpose κ hw] at h
    exact h
  · -- (H4)
    change E * Q.transpose + P * (chat κ x ρ).transpose
      = (0 : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    ext r zb
    obtain ⟨J, c⟩ := zb
    obtain ⟨g, rfl⟩ := hκ c
    have h := congrFun (congrFun hTR r) ((J, g) : Fin 4 × G)
    rw [Matrix.add_apply, Matrix.zero_apply, mul_colStrip_transpose_apply,
      rowStrip_mul_core_transpose] at h
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact h

/-! ### Theorem A -/

/-- **Theorem A** (`NOTE-B` §1.1), both directions.

Let `κ : G →+ Ḡ` be a surjective hom all of whose fibers have size `w`, let
`ρ ∈ G`, and let the corner `E`, the border tables `P` and `Q` and the seed
quadruple `x` be sign valued.  Then the bordered array

```
H = [ E   P̃ ]
    [ Q̃   C ]
```

is a Hadamard matrix (necessarily of order `N = 4(|G| + s)`) **if and only if**

* **(H1)** there is `M : Ḡ → ℤ` with `Q Qᵀ = I₄ ⊗ M`, and
* **(H2)** `Σ PAF(t) = −M(κ t)` for every `t ≠ 0`, and
* **(H3)** `E Eᵀ + w · P Pᵀ = N · I`, and
* **(H4)** `E Qᵀ + P Ĉᵀ = 0`, with `Ĉ = GS(σ₀,…,σ₃; κρ)` the compressed core.

`M` is automatically symmetric (`M_symm`) and satisfies `M 0 = 4s`
(`M_zero_of_H1`), so the "`−4s` on `K ∖ {0}`" tier of the profile is forced by
the ansatz rather than chosen.

The sufficiency direction does **not** need `κ` surjective; it is available
separately as `theoremA_sufficiency`. -/
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
  constructor
  · intro hH
    exact theoremA_necessity κ hκ hw E P Q x ρ
      ((border_isHadamard_iff_gram κ E P Q x ρ hE hP hQ hx).mp hH)
  · rintro ⟨⟨M, h1, h2⟩, h3, h4⟩
    exact theoremA_sufficiency κ hw E P Q x ρ hE hP hQ hx M h1 h2 h3 h4

end HadamardBFormalCore
