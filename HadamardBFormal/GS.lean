/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import HadamardBFormal.Develop

/-!
# The Goethals--Seidel core, in the standard orientation

`NOTE-B` §1.0 displays the core `C = GS(x₀,x₁,x₂,x₃; ρ)` as

```
       [  A     BR     CR     DR  ]
       [ -BR     A    DᵀR   -CᵀR  ]        A = dev x₀, B = dev x₁,
       [ -CR   -DᵀR    A     BᵀR  ]        C = dev x₂, D = dev x₃
       [ -DR    CᵀR  -BᵀR     A   ]
```

This is the note's **standard** orientation.  It differs from the sibling
repository `Hadamard-formal` (`goethalsSeidelBlock`), which uses the SageMath
orientation: the six transposed blocks carry the opposite sign there.  The table
below is the note's, cross-checked against `Hadamard-B/tools/bordered_gs.py`
(`gs_array`).

The file also carries **Lemma 2** (`NOTE-B` §1.1), the *seed-independent* block
Gram of the array:

* `gs_block_mul_transpose` : for arbitrary blocks lying in a common commutative
  algebra and type one for the reversal, `∑ₖ B a k (B b k)ᵀ = δ_{a,b} ∑ₖ Xₖ Xₖᵀ`;
* `core_gram_block` / `core_gram` : the specialisation to `Xq = dev xq`,
  `r = R_ρ`, where the right-hand side becomes `Σ PAF(g − h)`.

No hypothesis on the seeds enters: the sixteen-block sign bookkeeping is
seed-independent, and the aggregate `Σ PAF` is the only channel through which the
seeds reach the Gram.  The proof is the orientation-flipped port of
`Hadamard-formal`'s `goethalsSeidel_block_mul_transpose`.
-/

namespace HadamardBFormalCore

open scoped BigOperators Matrix

/-- The four-by-four table of blocks of the Goethals--Seidel array, in the
**standard** orientation of `NOTE-B` §1.0. -/
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

@[simp]
theorem gs_apply {G : Type*} (r : Equiv.Perm G) (X : Fin 4 → Matrix G G ℤ)
    (i j : Fin 4 × G) : gs r X i j = gsBlock r X i.1 j.1 i.2 j.2 :=
  rfl

/-- The core `C = GS(x₀,x₁,x₂,x₃; ρ)` of a seed quadruple over an abelian group. -/
def core {G : Type*} [AddCommGroup G] (x : Fin 4 → G → ℤ) (ρ : G) :
    Matrix (Fin 4 × G) (Fin 4 × G) ℤ :=
  gs (reflect ρ) fun q => dev (x q)

@[simp]
theorem core_apply {G : Type*} [AddCommGroup G] (x : Fin 4 → G → ℤ) (ρ : G)
    (i j : Fin 4 × G) :
    core x ρ i j = gsBlock (reflect ρ) (fun q => dev (x q)) i.1 j.1 i.2 j.2 :=
  rfl

/-! ### Signs -/

/-- Every entry of the array is one of the entries of the blocks, up to sign. -/
theorem gs_isSign {G : Type*} (r : Equiv.Perm G) (X : Fin 4 → Matrix G G ℤ)
    (hsign : ∀ a i j, IsSign (X a i j)) (i j : Fin 4 × G) : IsSign (gs r X i j) := by
  obtain ⟨a, i⟩ := i
  obtain ⟨b, j⟩ := j
  fin_cases a <;> fin_cases b <;> simp only [gs, gsBlock]
  all_goals first
    | exact hsign _ _ _
    | exact isSign_neg (hsign _ _ _)

/-- The core of a sign-valued quadruple is sign valued. -/
theorem core_isSign {G : Type*} [AddCommGroup G] (x : Fin 4 → G → ℤ) (ρ : G)
    (hx : ∀ q g, IsSign (x q g)) (i j : Fin 4 × G) : IsSign (core x ρ i j) :=
  gs_isSign _ _ (fun a i j => hx a (j - i)) i j

/-! ### Lemma 2: the block Gram -/

/-- The Gram entry of the array at a pair of block positions is the corresponding
entry of the block Gram. -/
theorem gs_mul_transpose_apply {G : Type*} [Fintype G] (r : Equiv.Perm G)
    (X : Fin 4 → Matrix G G ℤ) (a b : Fin 4) (i j : G) :
    (gs r X * (gs r X).transpose) (a, i) (b, j) =
      (∑ k, gsBlock r X a k * (gsBlock r X b k).transpose) i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, gs_apply, Matrix.sum_apply]
  rw [← Finset.sum_product' Finset.univ Finset.univ]
  simp only [Finset.univ_product_univ]

/-- **Lemma 2** (`NOTE-B` §1.1), seed-independent form.  If the four blocks lie in
a common commutative algebra together with their transposes and are type one for
the reversal, then the block Gram of the Goethals--Seidel array is
`δ_{a,b} · ∑ₖ Xₖ Xₖᵀ`.

Nothing but the algebra of the blocks is used, so **no hypothesis on the seeds
enters**.  This is the orientation-flipped port of `Hadamard-formal`'s
`goethalsSeidel_block_mul_transpose`. -/
theorem gs_block_mul_transpose {G : Type*} [Fintype G] (r : Equiv.Perm G)
    (hr : Function.Involutive r) (X : Fin 4 → Matrix G G ℤ)
    (hcomm : ∀ a b, X a * X b = X b * X a)
    (hcommTranspose : ∀ a b, X a * (X b).transpose = (X b).transpose * X a)
    (htype : ∀ a, IsTypeOne r (X a)) (a b : Fin 4) :
    (∑ k, gsBlock r X a k * (gsBlock r X b k).transpose) =
      if a = b then ∑ k, X k * (X k).transpose else 0 := by
  have hcommTT : ∀ a b, (X a).transpose * (X b).transpose =
      (X b).transpose * (X a).transpose := by
    intro a b
    have h := congrArg Matrix.transpose (hcomm b a)
    simpa using h
  fin_cases a <;> fin_cases b <;>
    simp [gsBlock, Fin.sum_univ_four,
      mul_transpose_revCols r hr, revCols_mul_transpose r hr,
      revCols_revCols_mul r hr, revCols_revCols r hr,
      htype, isTypeOne_transpose r hr, hcomm, hcommTranspose, hcommTT] <;>
    abel

/-- **Lemma 2 for developed seeds.**  The block Gram of `C = GS(x₀,…,x₃; ρ)` is
`δ_{a,b} · ∑_q Xq Xqᵀ`, for every reflection shift `ρ` and arbitrary sequences. -/
theorem core_gram_block {G : Type*} [Fintype G] [AddCommGroup G] (x : Fin 4 → G → ℤ)
    (ρ : G) (a b : Fin 4) :
    (∑ k, gsBlock (reflect ρ) (fun q => dev (x q)) a k
        * (gsBlock (reflect ρ) (fun q => dev (x q)) b k).transpose) =
      if a = b then ∑ q, dev (x q) * (dev (x q)).transpose else 0 :=
  gs_block_mul_transpose (reflect ρ) (reflect_involutive ρ) (fun q => dev (x q))
    (fun p q => dev_mul_comm (x p) (x q)) (fun p q => dev_mul_transpose_comm (x p) (x q))
    (fun q => dev_isTypeOne ρ (x q)) a b

/-- **Lemma 2, entrywise.**  `C Cᵀ = I₄ ⊗ Σ` with `Σ[g,h] = Σ PAF(g − h)`. -/
theorem core_gram {G : Type*} [Fintype G] [AddCommGroup G] (x : Fin 4 → G → ℤ) (ρ : G)
    (a b : Fin 4) (g h : G) :
    (core x ρ * (core x ρ).transpose) (a, g) (b, h) =
      if a = b then sumPaf x (g - h) else 0 := by
  rw [core, gs_mul_transpose_apply, core_gram_block]
  by_cases hab : a = b
  · rw [if_pos hab, if_pos hab, Matrix.sum_apply, sumPaf]
    exact Finset.sum_congr rfl fun q _ => dev_mul_transpose_apply (x q) g h
  · rw [if_neg hab, if_neg hab, Matrix.zero_apply]

end HadamardBFormalCore
