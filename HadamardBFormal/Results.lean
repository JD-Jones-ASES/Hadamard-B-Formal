/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import HadamardBFormal.Data

/-!
# The `H(52)` gate instance, through Theorem A

`NOTE-B` §2.2, cert 03.  The kernel-checked hypotheses of `HadamardBFormal/Data.lean`
are fed to `theoremA_sufficiency`, producing

* `hadamard_52_bordered` — the bordered array of the gate record is a Hadamard
  matrix, and
* `hadamardExists_52` — hence a classical Hadamard matrix of order `52` exists.

The gate is the Theorem-D instance the four decoded `i = 2` records do not
exercise: a from-scratch `s = 1, i = 2` instance on the **non-cyclic** group
`G = ZMod 2 × ZMod 2 × ZMod 3` with `w = 6`, in the `ε = +1` branch (`κ ρ = 0`).
No novelty of existence is claimed at order 52 — the order is long settled; what
the witness does is instantiate the theorem.

**The proof boundary.**  The kernel never touches the assembled `52 × 52` matrix
or its `52³` product.  It checks `O(n²)` worth of hypotheses on a group of order
12 and the theorem does the rest, which is the whole point of routing an instance
through Theorem A rather than through a matrix multiplication.
-/

namespace HadamardBFormal.Data

open scoped BigOperators Matrix

open HadamardBFormal

/-- **The `H(52)` gate instance.**  The bordered Goethals--Seidel array of the gate
record is a Hadamard matrix of order `4(12+1) = 52`.

Everything the kernel evaluates is a hypothesis of Theorem A on a group of order
`12`; the Hadamard property itself is deduced, never computed. -/
theorem hadamard_52_bordered :
    Matrix.IsHadamard (border kappa52 E52 P52 Q52 seed52 rho52) := by
  refine theoremA_sufficiency (s := 1) (w := 6) kappa52 kappa52_fiber E52 P52 Q52 seed52 rho52
    E52_isSign P52_isSign Q52_isSign seed52_isSign (houseM 1) h1_52 h2_52 ?_ h4_52
  rw [show (4 : ℤ) * ((Fintype.card G52 : ℤ) + ((1 : ℕ) : ℤ)) = 52 from by
    rw [card_G52]; norm_num]
  exact h3_52

/-- The gate instance realises the genuine branch of Theorem D: the Gram table has
`M(1) = −4`, so the column table pair-negates onto a `4 × 4` Hadamard matrix `U`.

This is `theoremD_tables` read on the kernel-checked (H1) of the record — the
formal counterpart of cert 03's check of clauses (D-a)/(D-b) on the gate. -/
theorem gate52_columnTable :
    (∀ I : Fin 4, Q52 (I, 1) = -Q52 (I, 0)) ∧
      Matrix.IsHadamard (Matrix.of fun I c : Fin 4 => Q52 (I, 0) c) :=
  (theoremD_tables Q52 Q52_isSign (houseM 1) h1_52).2.2
    (houseM_of_ne 1 (by decide : (1 : ZMod 2) ≠ 0))

/-- The bordered array of the gate record has `4 + 4·12 = 52` rows. -/
theorem card_border52 : Fintype.card (Fin (4 * 1) ⊕ (Fin 4 × G52)) = 52 := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Fintype.card_fin, card_G52]

/-- **A Hadamard matrix of order 52 exists**, as a `Matrix (Fin 52) (Fin 52) ℤ`.

The witness is the gate array relabelled along `Fin 52`; the order is long settled
and no novelty is claimed, but the *route* is the point: the existence statement is
obtained from Theorem A applied to twelve-element data, with no `52 × 52` product
anywhere in the trust base. -/
theorem hadamardExists_52 : HadamardExists 52 :=
  ⟨_, isHadamardOn_reindex hadamard_52_bordered
    ((Fintype.equivFin _).trans (finCongr card_border52))⟩

/-! ### The order-20 boundary instance

`NOTE-B` §2.2, cert 05.  Same route, on `G = ZMod 2 × ZMod 2` with `K` the
diagonal subgroup and `w = 2s = 2` — the exact hypothesis boundary of D3.  Its
companion T2 is in the transpose-negated orientation and is out of scope by
construction; the exporter refuses to emit it. -/

/-- **The order-20 boundary instance T1.**  The bordered array of the boundary
record is a Hadamard matrix of order `4(4+1) = 20`.

Theorem A does not care that `w = 2s`: its hypotheses (H1)--(H4) are what they
are, and the `w > 2s` clause is a hypothesis of D3, not of Theorem A.  Nor does
it care that `K` is the diagonal rather than a coordinate kernel — that is the
payoff of modelling the quotient as a surjective hom. -/
theorem hadamard_20_bordered :
    Matrix.IsHadamard (border kappa20 E20 P20 Q20 seed20 rho20) := by
  refine theoremA_sufficiency (s := 1) (w := 2) kappa20 kappa20_fiber E20 P20 Q20 seed20 rho20
    E20_isSign P20_isSign Q20_isSign seed20_isSign (houseM 1) h1_20 h2_20 ?_ h4_20
  rw [show (4 : ℤ) * ((Fintype.card G20 : ℤ) + ((1 : ℕ) : ℤ)) = 20 from by
    rw [card_G20]; norm_num]
  exact h3_20

/-- The bordered array of the boundary record has `4 + 4·4 = 20` rows. -/
theorem card_border20 : Fintype.card (Fin (4 * 1) ⊕ (Fin 4 × G20)) = 20 := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Fintype.card_fin, card_G20]

/-- **A Hadamard matrix of order 20 exists**, from the boundary record. -/
theorem hadamardExists_20 : HadamardExists 20 :=
  ⟨_, isHadamardOn_reindex hadamard_20_bordered
    ((Fintype.equivFin _).trans (finCongr card_border20))⟩

end HadamardBFormal.Data
