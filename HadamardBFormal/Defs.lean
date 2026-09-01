/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.HadamardMatrix

/-!
# Core definitions for the bordered Goethals--Seidel formalization

This file fixes the conventions of `NOTE-B` §1.0.  Throughout, `G` is a finite
abelian group written additively and sequences are integer valued with the sign
condition carried separately by `IsSign`.

* `dev x` is the **type-1 development** `dev(x)[g,h] = x (h - g)`.
* `reflect ρ` is the reflection `R_ρ : k ↦ ρ - k`, an involution of `G`; the
  associated permutation matrix is the note's `R[k,h] = [k + h = ρ]`.
* `revCols r A` is `A R`, i.e. the column reversal `(A R)[g,h] = A[g, r h]`.
* `paf` is the periodic autocorrelation `PAF_x(t) = ∑_u x u * x (u + t)` and
  `sumPaf` its aggregate over a quadruple.
* `cosetSum κ x c = σ(c) = ∑_{κ g = c} x g`.

The `IsSign` / `IsHadamardOn` layer is ported from the sibling repository
`Hadamard-formal` (`HadamardFormal/Defs.lean`), whose conventions this file
matches on the nose.
-/

namespace HadamardBFormalCore

open scoped BigOperators Matrix

/-! ### Signs -/

/-- An integer is a Hadamard sign when it is `+1` or `-1`. -/
def IsSign (z : ℤ) : Prop :=
  z = 1 ∨ z = -1

/-- `IsSign` is computable, so concrete sign data can be checked by kernel
reduction. -/
instance instDecidableIsSign (z : ℤ) : Decidable (IsSign z) := by
  unfold IsSign
  infer_instance

/-- The negation of a sign is a sign. -/
theorem isSign_neg {z : ℤ} (hz : IsSign z) : IsSign (-z) := by
  rcases hz with hz | hz
  · right; simp [hz]
  · left; simp [hz]

/-- The product of two signs is a sign. -/
theorem IsSign.mul {a b : ℤ} (ha : IsSign a) (hb : IsSign b) : IsSign (a * b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [IsSign]

/-- An integer squaring to `1` is a sign. -/
theorem isSign_of_mul_self_eq_one {z : ℤ} (hz : z * z = 1) : IsSign z :=
  mul_self_eq_one_iff.mp hz

/-! ### Hadamard matrices -/

/-- A Hadamard matrix indexed by an arbitrary finite type.

This is the integer specialization of mathlib's `Matrix.IsHadamard`: its
unitary-entry condition is exactly `+1` or `-1`. -/
abbrev IsHadamardOn {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℤ) : Prop :=
  H.IsHadamard

/-- A classical integer Hadamard matrix of order `n`. -/
abbrev IsHadamard {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  IsHadamardOn H

/-- There exists a classical integer Hadamard matrix of order `n`. -/
def HadamardExists (n : ℕ) : Prop :=
  ∃ H : Matrix (Fin n) (Fin n) ℤ, IsHadamard H

/-- Simultaneously relabel the rows and columns of a square matrix. -/
def reindexSquare {ι κ : Type*} (e : ι ≃ κ) (H : Matrix ι ι ℤ) : Matrix κ κ ℤ :=
  Matrix.reindex e e H

@[simp]
theorem reindexSquare_apply {ι κ : Type*} (e : ι ≃ κ) (H : Matrix ι ι ℤ) (i j : κ) :
    reindexSquare e H i j = H (e.symm i) (e.symm j) :=
  rfl

/-- Entries of an integer Hadamard matrix are signs in the source sense. -/
theorem isSign_of_isHadamardOn {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℤ}
    (hH : IsHadamardOn H) (i j : ι) : IsSign (H i j) :=
  Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem i j)

/-- Hadamardness is preserved when the common row/column index type is relabelled. -/
theorem isHadamardOn_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {H : Matrix ι ι ℤ} (hH : IsHadamardOn H) (e : ι ≃ κ) :
    IsHadamardOn (reindexSquare e H) :=
  hH.reindex e e

/-- Reindex an arbitrary finite Hadamard matrix by the canonical equivalence with
`Fin (Fintype.card ι)`. -/
noncomputable def toFinMatrix {ι : Type*} [Fintype ι] (H : Matrix ι ι ℤ) :
    Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℤ :=
  reindexSquare (Fintype.equivFin ι) H

/-- The canonical `Fin` reindexing of a Hadamard matrix is Hadamard. -/
theorem isHadamard_toFin {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℤ}
    (hH : IsHadamardOn H) : IsHadamard (toFinMatrix H) :=
  isHadamardOn_reindex hH (Fintype.equivFin ι)

/-! ### Development, reflection, column reversal -/

/-- The type-1 development of a sequence: `dev(x)[g,h] = x (h - g)`. -/
def dev {G : Type*} [Sub G] (x : G → ℤ) : Matrix G G ℤ :=
  fun g h => x (h - g)

@[simp]
theorem dev_apply {G : Type*} [Sub G] (x : G → ℤ) (g h : G) : dev x g h = x (h - g) :=
  rfl

/-- The reflection `R_ρ : k ↦ ρ - k`, an involutive permutation of `G`.

The note's permutation matrix is `R[k,h] = [k + h = ρ]`; acting on columns it is
`revCols (reflect ρ)`. -/
def reflect {G : Type*} [AddCommGroup G] (ρ : G) : Equiv.Perm G :=
  Equiv.subLeft ρ

@[simp]
theorem reflect_apply {G : Type*} [AddCommGroup G] (ρ h : G) : reflect ρ h = ρ - h :=
  rfl

/-- Reverse the columns of a square matrix along a permutation: `(A R)[g,h] = A[g, r h]`. -/
def revCols {G : Type*} (r : Equiv.Perm G) (A : Matrix G G ℤ) : Matrix G G ℤ :=
  fun g h => A g (r h)

@[simp]
theorem revCols_apply {G : Type*} (r : Equiv.Perm G) (A : Matrix G G ℤ) (g h : G) :
    revCols r A g h = A g (r h) :=
  rfl

/-! ### Correlations and coset sums -/

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

end HadamardBFormalCore
