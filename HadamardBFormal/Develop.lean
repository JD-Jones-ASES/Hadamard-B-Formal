/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import HadamardBFormal.Defs

/-!
# Lemma 1: the algebra of group-developed matrices

This is `NOTE-B` §1.1, Lemma 1(a)--(d), for an arbitrary reflection shift `ρ`.

* (a) `dev_mul_comm` : `X Y = Y X`.
* (b) `dev_mul_transpose_comm` : `X Yᵀ = Yᵀ X`, and `dev_mul_transpose_apply` :
  `(X Xᵀ)[g,h] = PAF_x (g - h)`.
* (c)/(d) are packaged as the four `revCols` identities
  `revCols_mul_transpose_revCols`, `mul_transpose_revCols`, `revCols_mul_transpose`
  and `revCols_revCols_mul`, exactly as in the sibling repository.  Those four are
  proved from `IsTypeOne` and involutivity of the reversal **only**, hence are
  automatically generic in `ρ`; the only new input here is
  `dev_isTypeOne`, i.e. `x (i - (ρ - j)) = x (j - (ρ - i))`.

Also here, because everything downstream needs it: `paf_zero` and `sumPaf_zero`,
the note's "at `t = 0` the sum is `4n` automatically".

The proofs of `dev_mul_comm`, `dev_mul_transpose_comm`, `dev_mul_transpose_apply`
and the four `revCols` identities are ported from `Hadamard-formal`
(`HadamardFormal/CooperWallis.lean`, `HadamardFormal/GoethalsSeidel.lean`) at the
same mathlib pin.

An alternative proof of (a) is mathlib's `Matrix.circulant_mul_comm`; the bridge to
mathlib's circulant module is recorded as `dev_eq_circulant_transpose`.
-/

namespace HadamardBFormal

open scoped BigOperators Matrix

/-! ### The bridge to `Matrix.circulant` -/

/-- `dev x` is the transpose of mathlib's `Matrix.circulant x`.

Mathlib's `Matrix.circulant v i j = v (i - j)`, so `(circulant x)ᵀ [g,h] = x (h - g)`.
Equivalently `dev x = Matrix.circulant fun t => x (-t)` by `Matrix.transpose_circulant`.
This is a citation lemma only: nothing below is routed through it. -/
theorem dev_eq_circulant_transpose {G : Type*} [Sub G] (x : G → ℤ) :
    dev x = (Matrix.circulant x)ᵀ :=
  rfl

/-! ### The reflection -/

/-- The reflection `k ↦ ρ - k` is an involution. -/
theorem reflect_involutive {G : Type*} [AddCommGroup G] (ρ : G) :
    Function.Involutive (reflect ρ) := by
  intro h
  simp only [reflect_apply]
  abel

/-! ### Type-one matrices -/

/-- The entrywise form of `Aᵀ R = R A`, where `R` is the permutation matrix of `r`. -/
def IsTypeOne {G : Type*} (r : Equiv.Perm G) (A : Matrix G G ℤ) : Prop :=
  ∀ i j, A (r j) i = A (r i) j

/-- Type-one-ness passes to the transpose. -/
theorem isTypeOne_transpose {G : Type*} (r : Equiv.Perm G) (hr : Function.Involutive r)
    {A : Matrix G G ℤ} (hA : IsTypeOne r A) : IsTypeOne r A.transpose := by
  intro i j
  change A i (r j) = A j (r i)
  have h := (hA (r i) (r j)).symm
  rw [hr i, hr j] at h
  exact h

/-- Every matrix developed over an abelian group is type one for every reflection
`R_ρ`.  This is the only place where genericity in `ρ` has to be checked. -/
theorem dev_isTypeOne {G : Type*} [AddCommGroup G] (ρ : G) (x : G → ℤ) :
    IsTypeOne (reflect ρ) (dev x) := by
  intro i j
  simp only [reflect_apply, dev_apply]
  congr 1
  abel

/-! ### Lemma 1(a), (b) -/

/-- Transposition reverses the developing sequence. -/
theorem dev_transpose {G : Type*} [AddCommGroup G] (x : G → ℤ) :
    (dev x).transpose = dev fun q => x (-q) := by
  ext i j
  change x (i - j) = x (-(j - i))
  congr 1
  abel

/-- **Lemma 1(a).** Matrices developed over the same finite abelian group commute. -/
theorem dev_mul_comm {G : Type*} [Fintype G] [AddCommGroup G] (x y : G → ℤ) :
    dev x * dev y = dev y * dev x := by
  ext i j
  simp only [Matrix.mul_apply, dev_apply]
  rw [← Equiv.sum_comp (Equiv.subLeft (i + j)) fun k => x (k - i) * y (j - k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  change x (i + j - k - i) * y (j - (i + j - k)) = y (k - i) * x (j - k)
  have h1 : i + j - k - i = j - k := by abel
  have h2 : j - (i + j - k) = k - i := by abel
  rw [h1, h2, mul_comm]

/-- **Lemma 1(b), first half.** A developed matrix commutes with every transposed
developed matrix. -/
theorem dev_mul_transpose_comm {G : Type*} [Fintype G] [AddCommGroup G] (x y : G → ℤ) :
    dev x * (dev y).transpose = (dev y).transpose * dev x := by
  rw [dev_transpose]
  exact dev_mul_comm _ _

/-- **Lemma 1(b), second half.** `(X Xᵀ)[g,h] = PAF_x (g - h)`. -/
theorem dev_mul_transpose_apply {G : Type*} [Fintype G] [AddCommGroup G] (x : G → ℤ)
    (i j : G) : (dev x * (dev x).transpose) i j = paf x (i - j) := by
  rw [Matrix.mul_apply]
  unfold paf
  rw [← Equiv.sum_comp (Equiv.addRight i)
    fun k => dev x i k * (dev x).transpose k j]
  refine Finset.sum_congr rfl fun q _ => ?_
  change x (q + i - i) * x (q + i - j) = x q * x (q + (i - j))
  congr 2 <;> abel_nf

/-! ### The profile at the origin -/

/-- `PAF_x(0) = |G|` for a sign-valued sequence. -/
theorem paf_zero {G : Type*} [Fintype G] [AddCommGroup G] {x : G → ℤ}
    (hx : ∀ g, IsSign (x g)) : paf x 0 = Fintype.card G := by
  have h : ∀ u : G, x u * x (u + 0) = 1 := by
    intro u
    rw [add_zero]
    rcases hx u with hu | hu <;> rw [hu] <;> norm_num
  rw [paf, Finset.sum_congr rfl fun u _ => h u]
  simp

/-- **`Σ PAF(0) = 4n` is automatic** (`NOTE-B` §1.1): the value of the aggregate
profile at the origin is forced by the sign condition alone. -/
theorem sumPaf_zero {G : Type*} [Fintype G] [AddCommGroup G] {x : Fin 4 → G → ℤ}
    (hx : ∀ q g, IsSign (x q g)) : sumPaf x 0 = 4 * (Fintype.card G : ℤ) := by
  rw [sumPaf, Finset.sum_congr rfl fun q _ => paf_zero (hx q)]
  simp

/-! ### Lemma 1(c), (d): the reflection identities -/

@[simp]
theorem revCols_neg {G : Type*} (r : Equiv.Perm G) (A : Matrix G G ℤ) :
    revCols r (-A) = -revCols r A :=
  rfl

/-- Reversing columns twice along an involution is the identity. -/
theorem revCols_revCols {G : Type*} (r : Equiv.Perm G) (hr : Function.Involutive r)
    (A : Matrix G G ℤ) : revCols r (revCols r A) = A := by
  ext i j
  simp only [revCols_apply]
  rw [hr j]

/-- Column reversal cancels in a Gram product. -/
theorem revCols_mul_transpose_revCols {G : Type*} [Fintype G] (r : Equiv.Perm G)
    (A B : Matrix G G ℤ) :
    revCols r A * (revCols r B).transpose = A * B.transpose := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, revCols_apply]
  exact Equiv.sum_comp r fun k => A i k * B j k

/-- `A (B R)ᵀ = (A B) R` for type-one `B`. -/
theorem mul_transpose_revCols {G : Type*} [Fintype G] (r : Equiv.Perm G)
    (hr : Function.Involutive r) (A B : Matrix G G ℤ) (hB : IsTypeOne r B) :
    A * (revCols r B).transpose = revCols r (A * B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, revCols_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have h := (hB (r j) (r k)).symm
  rw [hr j, hr k] at h
  exact h

/-- `(A R) Bᵀ = (A B) R` for type-one `B`. -/
theorem revCols_mul_transpose {G : Type*} [Fintype G] (r : Equiv.Perm G)
    (hr : Function.Involutive r) (A B : Matrix G G ℤ) (hB : IsTypeOne r B) :
    revCols r A * B.transpose = revCols r (A * B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, revCols_apply]
  calc
    ∑ k, A i (r k) * B j k = ∑ k, A i (r k) * B (r k) (r j) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      have h := (hB (r j) k).symm
      rw [hr j] at h
      exact h
    _ = ∑ k, A i k * B k (r j) := Equiv.sum_comp r fun k => A i k * B k (r j)

/-- `((A R) B) R = A Bᵀ` for type-one `B`. -/
theorem revCols_revCols_mul {G : Type*} [Fintype G] (r : Equiv.Perm G)
    (hr : Function.Involutive r) (A B : Matrix G G ℤ) (hB : IsTypeOne r B) :
    revCols r (revCols r A * B) = A * B.transpose := by
  ext i j
  simp only [revCols_apply, Matrix.mul_apply, Matrix.transpose_apply]
  calc
    ∑ k, A i (r k) * B k (r j) = ∑ k, A i (r k) * B (r (r k)) (r j) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hr k]
    _ = ∑ k, A i k * B (r k) (r j) := Equiv.sum_comp r fun k => A i k * B (r k) (r j)
    _ = ∑ k, A i k * B j k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      have h := hB (r j) k
      rw [hr j] at h
      exact h

end HadamardBFormal
