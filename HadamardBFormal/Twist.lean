/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import HadamardBFormal.Border

/-!
# Lemma T, the profile bijection, and the `ψ(ρ) = 1` conjugation

This is `NOTE-B` §1.4 in full.

* `lemmaT` : `PAF_{ψ x}(t) = ψ(t) · PAF_x(t)` for a character `ψ` with `ψ² = 1`.
* `twist_profile_iff` : at `s = 1` a quadruple satisfies the `i = 1` profile
  (`Σ PAF(t) = -4` for `t ≠ 0`) **iff** its twist satisfies the `i = 2` profile
  (`-4` on `ker κ ∖ {0}`, `+4` off `ker κ`).  The twist is an involution, so this
  is a bijection of seed problems.
* `twist_isConjugation` : if moreover `ψ(ρ) = 1`, the twisted bordered instance
  `x' = ψ x`, `P' = P D̄`, `Q' = D̄ Q`, `E' = E` assembles to `S H S` with
  `S = diag(I_{4s}, I₄ ⊗ diag ψ)`.
* `twist_isHadamard_iff` : hence a `ψ(ρ) = 1` twist manufactures nothing new — the
  twisted border is Hadamard exactly when the original is.

`ψ` is an `AddChar G ℤ`; the hypothesis `hsq : ∀ g, ψ g * ψ g = 1` carries `ψ² = 1`.
The factorisation of `ψ` through the quotient is supplied as **data** (`ψbar`
together with `hfac`), which is exactly what the border strips need.
-/

namespace HadamardBFormal

open scoped BigOperators Matrix

/-! ### Elementary consequences of `ψ² = 1` -/

section Character

variable {G : Type*} [AddCommGroup G] (ψ : AddChar G ℤ)

/-- A `±1`-valued character is nowhere zero. -/
theorem psi_ne_zero (hsq : ∀ g : G, ψ g * ψ g = 1) (g : G) : ψ g ≠ 0 := by
  intro h
  have h1 := hsq g
  rw [h, mul_zero] at h1
  exact zero_ne_one h1

/-- A character with `ψ² = 1` is even. -/
theorem psi_neg (hsq : ∀ g : G, ψ g * ψ g = 1) (g : G) : ψ (-g) = ψ g := by
  refine mul_left_cancel₀ (psi_ne_zero ψ hsq g) ?_
  rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, hsq]

/-- A character with `ψ² = 1` turns differences into products. -/
theorem psi_sub (hsq : ∀ g : G, ψ g * ψ g = 1) (a b : G) : ψ (a - b) = ψ a * ψ b := by
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, psi_neg ψ hsq]

/-- Every value of a character with `ψ² = 1` is a sign. -/
theorem psi_isSign (hsq : ∀ g : G, ψ g * ψ g = 1) (g : G) : IsSign (ψ g) :=
  isSign_of_mul_self_eq_one (hsq g)

/-- Under `ψ(ρ) = 1` the character is invariant along the reflection `R_ρ`.  This is
the exact content of the hypothesis `ψ(ρ) = 1` in the `NOTE-B` §1.4 proposition. -/
theorem psi_reflect (hsq : ∀ g : G, ψ g * ψ g = 1) (ρ : G) (hρ : ψ ρ = 1) (h : G) :
    ψ (reflect ρ h) = ψ h := by
  rw [reflect_apply, psi_sub ψ hsq, hρ, one_mul]

end Character

/-! ### Lemma T and the profile bijection -/

/-- **Lemma T** (`NOTE-B` §1.4).  For a character `ψ` with `ψ² = 1`,
`PAF_{ψ x}(t) = ψ(t) · PAF_x(t)`. -/
theorem lemmaT {G : Type*} [AddCommGroup G] [Fintype G] (ψ : AddChar G ℤ)
    (hsq : ∀ g : G, ψ g * ψ g = 1) (x : G → ℤ) (t : G) :
    paf (fun g => ψ g * x g) t = ψ t * paf x t := by
  unfold paf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  change ψ u * x u * (ψ (u + t) * x (u + t)) = ψ t * (x u * x (u + t))
  rw [AddChar.map_add_eq_mul]
  calc ψ u * x u * (ψ u * ψ t * x (u + t))
      = ψ u * ψ u * (ψ t * (x u * x (u + t))) := by ring
    _ = ψ t * (x u * x (u + t)) := by rw [hsq u, one_mul]

/-- The aggregate profile of a twisted quadruple. -/
theorem sumPaf_twist {G : Type*} [AddCommGroup G] [Fintype G] (ψ : AddChar G ℤ)
    (hsq : ∀ g : G, ψ g * ψ g = 1) (x : Fin 4 → G → ℤ) (t : G) :
    sumPaf (fun q g => ψ g * x q g) t = ψ t * sumPaf x t := by
  unfold sumPaf
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => lemmaT ψ hsq (x q) t

/-- **The `s = 1` profile bijection** (`NOTE-B` §1.4).  A quadruple satisfies the
`i = 1` profile `Σ PAF(t) = -4` off the origin iff its `ψ`-twist satisfies the
`i = 2` profile: `-4` on `ker κ ∖ {0}` and `+4` off `ker κ`. -/
theorem twist_profile_iff {G : Type*} [AddCommGroup G] [Fintype G] (ψ : AddChar G ℤ)
    (hsq : ∀ g : G, ψ g * ψ g = 1) (κ : G →+ ZMod 2)
    (hψ : ∀ g : G, ψ g = if κ g = 0 then 1 else -1) (x : Fin 4 → G → ℤ) :
    (∀ t : G, t ≠ 0 → sumPaf x t = -4) ↔
      ∀ t : G, t ≠ 0 → sumPaf (fun q g => ψ g * x q g) t = if κ t = 0 then -4 else 4 := by
  have key : ∀ t : G, (if κ t = 0 then (-4 : ℤ) else 4) = ψ t * (-4) := by
    intro t
    rw [hψ t]
    by_cases h : κ t = 0 <;> simp [h]
  constructor
  · intro h t ht
    rw [sumPaf_twist ψ hsq, h t ht, key t]
  · intro h t ht
    have h1 := h t ht
    rw [sumPaf_twist ψ hsq, key t] at h1
    exact mul_left_cancel₀ (psi_ne_zero ψ hsq t) h1

/-! ### Conjugation by a diagonal of signs -/

section DiagonalConj

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise form of conjugation by a diagonal matrix. -/
theorem diagonal_conj_apply (d : ι → ℤ) (A : Matrix ι ι ℤ) (i j : ι) :
    (Matrix.diagonal d * A * Matrix.diagonal d) i j = d i * A i j * d j := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- A diagonal of signs squares to the identity. -/
theorem diagonal_mul_self (d : ι → ℤ) (hd : ∀ i, d i * d i = 1) :
    Matrix.diagonal d * Matrix.diagonal d = (1 : Matrix ι ι ℤ) := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  exact congrArg Matrix.diagonal (funext hd)

/-- Transposition commutes with conjugation by a diagonal. -/
theorem transpose_diagonal_conj (d : ι → ℤ) (A : Matrix ι ι ℤ) :
    (Matrix.diagonal d * A * Matrix.diagonal d).transpose =
      Matrix.diagonal d * A.transpose * Matrix.diagonal d := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]

/-- Conjugation by a diagonal of signs is multiplicative. -/
theorem diagonal_conj_mul (d : ι → ℤ) (hd : ∀ i, d i * d i = 1) (A B : Matrix ι ι ℤ) :
    Matrix.diagonal d * A * Matrix.diagonal d * (Matrix.diagonal d * B * Matrix.diagonal d) =
      Matrix.diagonal d * (A * B) * Matrix.diagonal d := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.diagonal d) (Matrix.diagonal d),
    diagonal_mul_self d hd, Matrix.one_mul]

/-- Conjugation by a diagonal of signs is an involution. -/
theorem diagonal_conj_conj (d : ι → ℤ) (hd : ∀ i, d i * d i = 1) (A : Matrix ι ι ℤ) :
    Matrix.diagonal d * (Matrix.diagonal d * A * Matrix.diagonal d) * Matrix.diagonal d = A := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.diagonal d) (Matrix.diagonal d),
    diagonal_mul_self d hd, Matrix.one_mul, Matrix.mul_one]

private theorem isHadamard_diagonal_conj (d : ι → ℤ) (hd : ∀ i, d i * d i = 1)
    {A : Matrix ι ι ℤ} (hA : Matrix.IsHadamard A) :
    Matrix.IsHadamard (Matrix.diagonal d * A * Matrix.diagonal d) := by
  have hsmul : ∀ c : ℤ,
      Matrix.diagonal d * (c • (1 : Matrix ι ι ℤ)) * Matrix.diagonal d = c • 1 := by
    intro c
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, diagonal_mul_self d hd]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [diagonal_conj_apply]
    exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
      (((isSign_of_mul_self_eq_one (hd i)).mul (isSign_of_isHadamardOn hA i j)).mul
        (isSign_of_mul_self_eq_one (hd j)))
  · rw [Matrix.conjTranspose_eq_transpose_of_trivial, transpose_diagonal_conj,
      diagonal_conj_mul d hd,
      show A * A.transpose = (Fintype.card ι : ℤ) • (1 : Matrix ι ι ℤ) by
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.mul_conjTranspose]
    exact hsmul _
  · rw [Matrix.conjTranspose_eq_transpose_of_trivial, transpose_diagonal_conj,
      diagonal_conj_mul d hd,
      show A.transpose * A = (Fintype.card ι : ℤ) • (1 : Matrix ι ι ℤ) by
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.conjTranspose_mul]
    exact hsmul _

/-- Conjugating by a diagonal of signs preserves and reflects Hadamardness. -/
theorem isHadamard_diagonal_conj_iff (d : ι → ℤ) (hd : ∀ i, d i * d i = 1)
    (A : Matrix ι ι ℤ) :
    Matrix.IsHadamard (Matrix.diagonal d * A * Matrix.diagonal d) ↔ Matrix.IsHadamard A := by
  refine ⟨fun h => ?_, fun h => isHadamard_diagonal_conj d hd h⟩
  have h2 := isHadamard_diagonal_conj d hd h
  rwa [diagonal_conj_conj d hd] at h2

end DiagonalConj

/-! ### The twisted core scales entrywise -/

/-- The Goethals--Seidel table intertwines an entrywise rank-one scaling, provided
the scaling vector is invariant along the reversal.  Both the plain and the
transposed blocks pick up exactly `d g * d h`; the six sign flips of the standard
orientation are untouched. -/
theorem gsBlock_scale {G : Type*} (d : G → ℤ) (r : Equiv.Perm G) (hr : ∀ h, d (r h) = d h)
    (X X' : Fin 4 → Matrix G G ℤ) (hX : ∀ q g h, X' q g h = d g * X q g h * d h)
    (I J : Fin 4) (g h : G) :
    gsBlock r X' I J g h = d g * gsBlock r X I J g h * d h := by
  fin_cases I <;> fin_cases J <;>
    simp only [gsBlock, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.neg_apply, revCols_apply, Matrix.transpose_apply,
      hX, hr, mul_neg, neg_mul, neg_inj] <;>
    ring

/-- **The twisted core is the diagonal conjugate of the core** — the block
computation of the `NOTE-B` §1.4 proposition:
`A'[g,h] = ψ(g)ψ(h)A[g,h]`, `(BR)'[g,h] = ψ(ρ)ψ(g)ψ(h)(BR)[g,h]`,
`(XᵀR)'[g,h] = ψ(g)ψ(h)(XᵀR)[g,h]`. -/
theorem core_twist {G : Type*} [AddCommGroup G] (ψ : AddChar G ℤ)
    (hsq : ∀ g : G, ψ g * ψ g = 1) (x : Fin 4 → G → ℤ) (ρ : G) (hρ : ψ ρ = 1)
    (I J : Fin 4) (g h : G) :
    core (fun q k => ψ k * x q k) ρ (I, g) (J, h) = ψ g * core x ρ (I, g) (J, h) * ψ h := by
  refine gsBlock_scale (fun k : G => ψ k) (reflect ρ) (psi_reflect ψ hsq ρ hρ)
    (fun q => dev (x q)) (fun q => dev fun k => ψ k * x q k) ?_ I J g h
  intro q a b
  simp only [dev_apply]
  rw [psi_sub ψ hsq]
  ring

/-! ### The conjugation proposition -/

/-- The diagonal `D̄ = diag(ψ̄(c))` acting on the border tables over the quotient. -/
def twistDiagBar {Gbar : Type*} [DecidableEq Gbar] (ψbar : Gbar → ℤ) :
    Matrix (Fin 4 × Gbar) (Fin 4 × Gbar) ℤ :=
  Matrix.diagonal fun z : Fin 4 × Gbar => ψbar z.2

/-- The conjugator `S = diag(I_{4s}, I₄ ⊗ diag ψ)` of the `NOTE-B` §1.4
proposition. -/
def twistConj {G : Type*} [AddCommGroup G] [DecidableEq G] (s : ℕ) (ψ : AddChar G ℤ) :
    Matrix (Fin (4 * s) ⊕ (Fin 4 × G)) (Fin (4 * s) ⊕ (Fin 4 × G)) ℤ :=
  Matrix.fromBlocks 1 0 0 (Matrix.diagonal fun z : Fin 4 × G => ψ z.2)

/-- The sign vector carried by `twistConj`. -/
def twistDiagVec {G : Type*} [AddCommGroup G] (s : ℕ) (ψ : AddChar G ℤ) :
    Fin (4 * s) ⊕ (Fin 4 × G) → ℤ :=
  Sum.elim (fun _ => 1) fun z : Fin 4 × G => ψ z.2

/-- `S` is the diagonal matrix of `twistDiagVec`. -/
theorem twistConj_eq_diagonal {G : Type*} [AddCommGroup G] [DecidableEq G] (s : ℕ)
    (ψ : AddChar G ℤ) : twistConj s ψ = Matrix.diagonal (twistDiagVec s ψ) := by
  rw [twistConj, twistDiagVec, ← Matrix.diagonal_one, Matrix.fromBlocks_diagonal]

/-- Every entry of `twistDiagVec` is a sign. -/
theorem twistDiagVec_mul_self {G : Type*} [AddCommGroup G] (s : ℕ) (ψ : AddChar G ℤ)
    (hsq : ∀ g : G, ψ g * ψ g = 1) (i : Fin (4 * s) ⊕ (Fin 4 × G)) :
    twistDiagVec s ψ i * twistDiagVec s ψ i = 1 := by
  cases i with
  | inl r => simp [twistDiagVec]
  | inr z => simpa [twistDiagVec] using hsq z.2

/-- **A twist with `ψ(ρ) = 1` is a diagonal conjugation** (`NOTE-B` §1.4,
Proposition).  The twisted instance `x' = ψ x`, `P' = P D̄`, `Q' = D̄ Q`, `E' = E`
assembles to `S H S`. -/
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
  rw [twistConj_eq_diagonal]
  ext i j
  rw [diagonal_conj_apply]
  cases i with
  | inl r =>
    cases j with
    | inl c => simp [border, twistDiagVec]
    | inr z =>
      simp only [border, Matrix.fromBlocks_apply₁₂, rowStrip_apply, twistDiagVec,
        Sum.elim_inl, Sum.elim_inr, one_mul]
      rw [twistDiagBar, Matrix.mul_diagonal, hfac z.2]
  | inr z =>
    cases j with
    | inl c =>
      simp only [border, Matrix.fromBlocks_apply₂₁, colStrip_apply, twistDiagVec,
        Sum.elim_inl, Sum.elim_inr, mul_one]
      rw [twistDiagBar, Matrix.diagonal_mul, hfac z.2]
    | inr y =>
      simp only [border, Matrix.fromBlocks_apply₂₂, twistDiagVec, Sum.elim_inr]
      exact core_twist ψ hsq x ρ hρ z.1 y.1 z.2 y.2

/-- **The twist manufactures nothing new when `ψ(ρ) = 1`**: the twisted bordered
array is Hadamard exactly when the original is. -/
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
  rw [twist_isConjugation κ ψ hsq ψbar hfac ρ hρ E P Q x, twistConj_eq_diagonal]
  exact isHadamard_diagonal_conj_iff _ (twistDiagVec_mul_self s ψ hsq) _

end HadamardBFormal
