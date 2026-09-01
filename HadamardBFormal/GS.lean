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

Only the definitions live in this file; the Gram theorem is a later stage.
-/

namespace HadamardBFormal

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

end HadamardBFormal
