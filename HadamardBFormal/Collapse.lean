/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import HadamardBFormal.TheoremA
import HadamardBFormal.TheoremD

/-!
# Transport across the doubling, and the index-two collapse

`NOTE-B` §1.5 (D-e) and §1.6.  Four compared declarations, all about the *same*
phenomenon: at `s = 1` the index-one and index-two border systems are one
system.

* `theoremD_transport` — the transport half of **(D-e)**.  Given an `s = 1, i = 1`
  bordered instance `(E₁, P₁, Q₁)` for seeds `x`, the **doubled** tables

  ```
  P[r][(J,c)] = (−1)^c · P₁[r][J],   Q[(I,0)] = Q₁[I],   Q[(I,1)] = −Q₁[I],   E = E₁
  ```

  together with the **`ψ`-twisted** seeds `ψ x` form a valid `i = 2` bordered
  instance — Hadamard of the same order `4(n+1)`.  The note's hypothesis for this
  is `d = r`: the transported border equation reads `P₁Λ(d)ᵀ = P₁Λ(r)ᵀ`, so it
  holds exactly when the twisted vector `d` of the `i = 2` system equals the
  row-sum vector `r` of the `i = 1` system.  That hypothesis is carried here as
  `hd`.  It is automatic when `κ ρ = 0` (the `ε = +1` branch), because
  `δ_q(ψ x) = r_q(x)`: see `dvec_seedTwist_of_eps_one` and the corollary
  `theoremD_transport_eps_one`.

* `theoremD_transport_converse` — the other half of **(D-e)**: `d = r` is *forced*.
  The transported border equation reads `P₁Λ(d)ᵀQ₁ = P₁Λ(r)ᵀQ₁`, and cancelling the
  two `4 × 4` Hadamard factors — over `ℤ`, not over `ℚ` — gives `Λ(d) = Λ(r)`.
  `theoremD_transport_iff` packages the two halves as the note's *exactly when*.

* `collapse_seedProblem_bijection` — the seed-problem bijection clause of
  §1.6's Corollary.  The twist `x ↦ ψ x` is an
  involution of sign-valued quadruples carrying the `i = 1` seed problem
  (`Σ PAF(t) = −4` off the origin) onto the `i = 2` seed problem (the house
  profile at `s = 1`).  The two seed problems are one problem.

  Like `twist_profile_iff`, this is stated for **any** `κ : G →+ ZMod 2`, not
  only a surjective one — a strengthening, and one worth reading precisely.  For
  a non-surjective `κ` the kernel is all of `G`, `ψ ≡ 1`, the twist is the
  identity, and the statement holds trivially with the "`i = 2` profile"
  degenerating back to the `i = 1` profile.  The **index-two** reading is the
  surjective case; unrestricted, the object is a `ZMod 2`-coded profile.

**Not formalized here** (future work — the rest of `NOTE-B` §1.6's Corollary): when the
index-two subgroup `K` is *unique* it is characteristic, so `ψ ∘ α = ψ` for every
`α ∈ Aut G` and the bijection commutes with every multiplier subgroup.  That
upgrade is group-theoretic API archaeology (`Subgroup.index_eq_two_iff`,
`Subgroup.index_mul_card`) and adds nothing to the bijection itself.

The proof of `theoremD_transport` uses no new machinery: `theoremD_border`
(`TheoremD.lean`) turns (H4) into the single `4 × 4` equation, `lemmaT` through
`sumPaf_twist` transports the profile, and `theoremA_sufficiency` assembles.
-/

namespace HadamardBFormalCore

open scoped BigOperators Matrix

/-! ### The twisted quadruple -/

/-- The `ψ`-twist of a seed quadruple, `x ↦ (g ↦ (−1)^{κ g} x_q(g))`. -/
def seedTwist {G : Type*} [AddCommGroup G] (κ : G →+ ZMod 2) (x : Fin 4 → G → ℤ) :
    Fin 4 → G → ℤ :=
  fun q g => psi2 κ g * x q g

@[simp]
theorem seedTwist_apply {G : Type*} [AddCommGroup G] (κ : G →+ ZMod 2) (x : Fin 4 → G → ℤ)
    (q : Fin 4) (g : G) : seedTwist κ x q g = psi2 κ g * x q g :=
  rfl

/-- The twist is an involution: `ψ(ψ x) = x`, since `ψ² = 1`. -/
theorem seedTwist_seedTwist {G : Type*} [AddCommGroup G] (κ : G →+ ZMod 2)
    (x : Fin 4 → G → ℤ) : seedTwist κ (seedTwist κ x) = x := by
  funext q g
  rw [seedTwist_apply, seedTwist_apply, ← mul_assoc, psi2_sq, one_mul]

/-- Sign-valuedness is preserved and reflected by the twist. -/
theorem seedTwist_isSign_iff {G : Type*} [AddCommGroup G] (κ : G →+ ZMod 2)
    (x : Fin 4 → G → ℤ) : (∀ q g, IsSign (x q g)) ↔ ∀ q g, IsSign (seedTwist κ x q g) := by
  constructor
  · intro h q g
    rw [seedTwist_apply]
    exact (psi_isSign (psi2 κ) (psi2_sq κ) g).mul (h q g)
  · intro h q g
    have hx : x q g = psi2 κ g * seedTwist κ x q g := by
      rw [seedTwist_apply, ← mul_assoc, psi2_sq, one_mul]
    rw [hx]
    exact (psi_isSign (psi2 κ) (psi2_sq κ) g).mul (h q g)

/-- The aggregate profile of the twist, `Σ PAF_{ψx}(t) = ψ(t) Σ PAF_x(t)` — `lemmaT`
read on the quadruple. -/
theorem sumPaf_seedTwist {G : Type*} [AddCommGroup G] [Fintype G] (κ : G →+ ZMod 2)
    (x : Fin 4 → G → ℤ) (t : G) :
    sumPaf (seedTwist κ x) t = psi2 κ t * sumPaf x t :=
  sumPaf_twist (psi2 κ) (psi2_sq κ) x t

/-- **The twist exchanges `δ` and `r`.**  The twisted coset difference of `ψ x` is the
plain row sum of `x`: `δ_q(ψ x) = Σ_g x_q(g) = r_q(x)`. -/
theorem delta_seedTwist {G : Type*} [AddCommGroup G] [Fintype G] (κ : G →+ ZMod 2)
    (y : G → ℤ) : delta κ (fun g => psi2 κ g * y g) = ∑ g, y g := by
  rw [← delta_eq κ fun g => psi2 κ g * y g]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← mul_assoc, psi2_sq, one_mul]

/-- In the `ε = +1` branch the twisted vector `d` of the `i = 2` system **is** the
row-sum vector `r` of the `i = 1` system — the note's `d = r`. -/
theorem dvec_seedTwist_of_eps_one {G : Type*} [AddCommGroup G] [Fintype G]
    (κ : G →+ ZMod 2) (x : Fin 4 → G → ℤ) {ρ : G} (hρ : κ ρ = 0) :
    dvec κ (seedTwist κ x) ρ = rvec x := by
  have hd : ∀ q : Fin 4, delta κ (seedTwist κ x q) = rvec x q := fun q =>
    delta_seedTwist κ (x q)
  funext q
  fin_cases q <;>
    simp only [dvec, rvec, eps_of_zero hρ, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    exact hd _

/-! ### The doubled border tables -/

/-- The doubled row table `P[r][(J,c)] = (−1)^c · P₁[r][J]` (`NOTE-B` §1.5, (D-e)). -/
def doubleRow (P : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ :=
  fun r z => if z.2 = 0 then P r z.1 else -P r z.1

/-- The doubled column table `Q[(I,0)] = Q₁[I]`, `Q[(I,1)] = −Q₁[I]`. -/
def doubleCol (Q : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin 4 × ZMod 2) (Fin (4 * 1)) ℤ :=
  fun z c => if z.2 = 0 then Q z.1 c else -Q z.1 c

/-- `1 ≠ 0` in `ZMod 2`, as a standalone fact so that the `if`-elimination lemmas below
do not have to `decide` under a binder. -/
private theorem zmod2_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

private theorem zmod2_zero_ne_one : (0 : ZMod 2) ≠ 1 := by decide

/-- The house Gram table at `s = 1` and index two, evaluated on a difference of
classes: `M(c − c′) = 4` when the classes agree and `−4` otherwise. -/
private theorem houseM_one_sub (c c' : ZMod 2) :
    houseM (Gbar := ZMod 2) 1 (c - c') = if c = c' then (4 : ℤ) else -4 := by
  by_cases h : c = c'
  · subst h
    rw [sub_self, houseM_zero, if_pos rfl]
    norm_num
  · rw [houseM_of_ne 1 (sub_ne_zero_of_ne h), if_neg h]

@[simp]
theorem doubleRow_zero (P : Matrix (Fin 4) (Fin 4) ℤ) (r : Fin (4 * 1)) (J : Fin 4) :
    doubleRow P r (J, 0) = P r J :=
  if_pos rfl

@[simp]
theorem doubleRow_one (P : Matrix (Fin 4) (Fin 4) ℤ) (r : Fin (4 * 1)) (J : Fin 4) :
    doubleRow P r (J, 1) = -P r J :=
  if_neg zmod2_one_ne_zero

@[simp]
theorem doubleCol_zero (Q : Matrix (Fin 4) (Fin 4) ℤ) (I : Fin 4) (c : Fin (4 * 1)) :
    doubleCol Q (I, 0) c = Q I c :=
  if_pos rfl

@[simp]
theorem doubleCol_one (Q : Matrix (Fin 4) (Fin 4) ℤ) (I : Fin 4) (c : Fin (4 * 1)) :
    doubleCol Q (I, 1) c = -Q I c :=
  if_neg zmod2_one_ne_zero

theorem doubleRow_isSign {P : Matrix (Fin 4) (Fin 4) ℤ} (hP : ∀ r J, IsSign (P r J))
    (r : Fin (4 * 1)) (z : Fin 4 × ZMod 2) : IsSign (doubleRow P r z) := by
  rcases zmod2_cases z.2 with h | h
  · rw [show z = (z.1, (0 : ZMod 2)) from Prod.ext rfl h, doubleRow_zero]
    exact hP r z.1
  · rw [show z = (z.1, (1 : ZMod 2)) from Prod.ext rfl h, doubleRow_one]
    exact isSign_neg (hP r z.1)

theorem doubleCol_isSign {Q : Matrix (Fin 4) (Fin 4) ℤ} (hQ : ∀ I c, IsSign (Q I c))
    (z : Fin 4 × ZMod 2) (c : Fin (4 * 1)) : IsSign (doubleCol Q z c) := by
  rcases zmod2_cases z.2 with h | h
  · rw [show z = (z.1, (0 : ZMod 2)) from Prod.ext rfl h, doubleCol_zero]
    exact hQ z.1 c
  · rw [show z = (z.1, (1 : ZMod 2)) from Prod.ext rfl h, doubleCol_one]
    exact isSign_neg (hQ z.1 c)

/-- **The doubled column table satisfies (H1) with the house Gram table.**  This is the
converse half of (D-b): pair-negating a `4 × 4` Hadamard `Q₁` produces exactly the
`M = 8I₂ − 4J₂` Gram. -/
theorem doubleCol_H1 {Q : Matrix (Fin 4) (Fin 4) ℤ}
    (hQ : Q * Q.transpose = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    H1 (s := 1) (doubleCol Q) (houseM 1) := by
  have hQe : ∀ I J : Fin 4, (∑ e : Fin (4 * 1), Q I e * Q J e) = if I = J then (4 : ℤ) else 0 := by
    intro I J
    have h := congrFun (congrFun hQ I) J
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at h
    simp only [Matrix.transpose_apply] at h
    rw [h]
    by_cases hIJ : I = J
    · rw [if_pos hIJ, if_pos hIJ, mul_one]
    · rw [if_neg hIJ, if_neg hIJ, mul_zero]
  -- Each class index contributes an overall sign to the dot product.
  have hsum : ∀ (I J : Fin 4) (c c' : ZMod 2),
      (∑ e : Fin (4 * 1), doubleCol Q (I, c) e * doubleCol Q (J, c') e)
        = (if c = c' then (1 : ℤ) else -1) * (if I = J then (4 : ℤ) else 0) := by
    intro I J c c'
    rcases zmod2_cases c with hc | hc <;> rcases zmod2_cases c' with hc' | hc' <;>
      subst hc <;> subst hc'
    · rw [if_pos rfl, one_mul]
      simp only [doubleCol_zero]
      exact hQe I J
    · rw [if_neg zmod2_zero_ne_one]
      simp only [doubleCol_zero, doubleCol_one, mul_neg, Finset.sum_neg_distrib, hQe I J]
      ring
    · rw [if_neg zmod2_one_ne_zero]
      simp only [doubleCol_zero, doubleCol_one, neg_mul, Finset.sum_neg_distrib, hQe I J]
      ring
    · rw [if_pos rfl, one_mul]
      simp only [doubleCol_one, neg_mul, mul_neg, neg_neg]
      exact hQe I J
  intro a b
  obtain ⟨I, c⟩ := a
  obtain ⟨J, c'⟩ := b
  change (∑ e : Fin (4 * 1), doubleCol Q (I, c) e * doubleCol Q (J, c') e)
    = if I = J then houseM (Gbar := ZMod 2) 1 (c - c') else 0
  rw [hsum I J c c', houseM_one_sub]
  by_cases hIJ : I = J
  · rw [if_pos hIJ, if_pos hIJ]
    by_cases hcc : c = c'
    · rw [if_pos hcc, if_pos hcc]
      ring
    · rw [if_neg hcc, if_neg hcc]
      ring
  · rw [if_neg hIJ, if_neg hIJ]
    ring

/-- **The doubled row table doubles the Gram.**  `P Pᵀ = 2 · P₁ P₁ᵀ`, which is what turns
(H3) at fiber size `w` into (H3) at fiber size `n = 2w`. -/
theorem doubleRow_gram (P : Matrix (Fin 4) (Fin 4) ℤ) :
    doubleRow P * (doubleRow P).transpose
      = (2 : ℤ) • (P * P.transpose : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ) := by
  ext r t
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [zmod2_sum]
  simp only [doubleRow_zero, doubleRow_one, neg_mul, mul_neg, neg_neg]
  ring

/-! ### Transport across the doubling -/

/-- **Theorem D, the transport clause of (D-e)** (`NOTE-B` §1.5).

An `s = 1, i = 1` bordered instance `(E₁, P₁, Q₁)` for a sign-valued quadruple `x`
with the index-one profile `Σ PAF(t) = −4` off the origin transports across the
doubling: the doubled tables `doubleRow P₁`, `doubleCol Q₁`, the same corner `E₁`,
and the **twisted** seeds `ψ x` form a valid `s = 1, i = 2` bordered instance for
`κ : G →+ ZMod 2`.

The hypotheses are the index-one system in the note's own form:

* `hQgram` — (H1) at `i = 1`, i.e. `Q₁ Q₁ᵀ = 4·I₄`;
* `hprofile` — (H2) at `i = 1`, the profile `Σ PAF(t) = −4` off the origin;
* `h3` — (H3) at `i = 1`, `E₁ E₁ᵀ + n · P₁ P₁ᵀ = N · I₄`;
* `h4` — (H4) at `i = 1`, the border equation `E₁ Q₁ᵀ + P₁ Λ(r)ᵀ = 0`;
* `hd` — the note's `d = r`, which is exactly when the transported border is valid.

`hd` is not decoration: the transported system reads `P₁ Λ(d)ᵀ = P₁ Λ(r)ᵀ`, so with
`Λ` injective and `P₁` invertible it holds precisely when `d = r`.  In the `ε = +1`
branch it is automatic — see `theoremD_transport_eps_one`. -/
theorem theoremD_transport {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G] {w : ℕ}
    (κ : G →+ ZMod 2)
    (hw : ∀ c : ZMod 2, (Finset.univ.filter fun g : G => κ g = c).card = w)
    (E₁ : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ) (P₁ Q₁ : Matrix (Fin 4) (Fin 4) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G)
    (hE : ∀ r c, IsSign (E₁ r c)) (hP : ∀ r J, IsSign (P₁ r J)) (hQ : ∀ I c, IsSign (Q₁ I c))
    (hx : ∀ q g, IsSign (x q g))
    (hQgram : Q₁ * Q₁.transpose = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hprofile : ∀ t : G, t ≠ 0 → sumPaf x t = -4)
    (h3 : E₁ * E₁.transpose + (Fintype.card G : ℤ) • (P₁ * P₁.transpose)
      = (4 * ((Fintype.card G : ℤ) + 1)) • 1)
    (h4 : E₁ * Q₁.transpose + P₁ * (Lam (rvec x)).transpose = 0)
    (hd : dvec κ (seedTwist κ x) ρ = rvec x) :
    Matrix.IsHadamard (border κ E₁ (doubleRow P₁) (doubleCol Q₁) (seedTwist κ x) ρ) := by
  -- `n = 2w`, the index-two arithmetic.
  have hn : (Fintype.card G : ℤ) = 2 * (w : ℤ) := by
    have h := sum_comp_of_card_fiber_eq (⇑κ) hw fun _ => (1 : ℤ)
    rw [zmod2_sum] at h
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
    rw [h]
    ring
  have hx' : ∀ q g, IsSign (seedTwist κ x q g) := (seedTwist_isSign_iff κ x).mp hx
  -- (H1) for the doubled column table.
  have h1' : H1 (s := 1) (doubleCol Q₁) (houseM 1) := doubleCol_H1 hQgram
  -- (H2): the twist turns the index-one profile into the house profile.
  have h2' : H2 (seedTwist κ x) κ (houseM 1) := by
    intro t ht
    rw [sumPaf_seedTwist, hprofile t ht]
    rcases zmod2_cases (κ t) with hk | hk
    · rw [psi2_apply, if_pos hk, hk, houseM_zero]
      norm_num
    · rw [psi2_apply, if_neg (by rw [hk]; decide),
        houseM_of_ne 1 (by rw [hk]; decide)]
      norm_num
  -- (H3): the doubling turns the fiber size `w` into `n = 2w`.
  have h3' : H3 (s := 1) E₁ (doubleRow P₁) (w : ℤ) (4 * ((Fintype.card G : ℤ) + 1)) := by
    rw [H3, doubleRow_gram, smul_smul, show (w : ℤ) * 2 = (Fintype.card G : ℤ) from by
      rw [hn]; ring]
    exact h3
  -- `Q₁` is a `4 × 4` Hadamard matrix.
  have hQhad : Matrix.IsHadamard Q₁ := by
    refine Matrix.IsHadamard.of_mul_conjTranspose
      (fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (hQ i j)) ?_ ?_
    · rw [Matrix.conjTranspose_eq_transpose_of_trivial, hQgram]
      norm_num
    · rw [isRegular_iff_ne_zero]
      norm_num
  have hUTU : Q₁.transpose * Q₁ = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    have h := hQhad.conjTranspose_mul
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    simpa using h
  -- (H4): `theoremD_border` collapses it to the single `4 × 4` equation, which the
  -- index-one border equation supplies once `d = r`.
  have hUeq : (Matrix.of fun I c : Fin 4 => doubleCol Q₁ (I, 0) c) = Q₁ := by
    ext I c
    exact doubleCol_zero Q₁ I c
  have hpeq : (Matrix.of fun r J : Fin 4 => doubleRow P₁ r (J, 0)) = P₁ := by
    ext r J
    exact doubleRow_zero P₁ r J
  have h4' : H4 (s := 1) E₁ (doubleRow P₁) (doubleCol Q₁) (chat κ (seedTwist κ x) ρ) := by
    refine (theoremD_border κ (seedTwist κ x) ρ E₁ (doubleRow P₁) (doubleCol Q₁)
      (fun I => ?_) (fun r J => ?_) ?_).mpr ?_
    · funext c
      simp only [Pi.neg_apply, doubleCol_one, doubleCol_zero]
    · rw [doubleRow_one, doubleRow_zero]
    · rw [hUeq]
      exact hQhad
    · rw [hUeq, hpeq, hd]
      have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℤ => A * Q₁) h4
      simp only [Matrix.zero_mul] at h
      rw [Matrix.add_mul, Matrix.mul_assoc, hUTU, Matrix.mul_smul, Matrix.mul_one] at h
      rw [eq_neg_iff_add_eq_zero]
      exact h
  exact theoremA_sufficiency (s := 1) (w := w) κ hw E₁ (doubleRow P₁) (doubleCol Q₁)
    (seedTwist κ x) ρ hE (fun r z => doubleRow_isSign hP r z)
    (fun z c => doubleCol_isSign hQ z c) hx' (houseM 1) h1' h2' h3' h4'

/-- **Transport in the `ε = +1` branch.**  When `κ ρ = 0` the note's condition `d = r`
is automatic, because the twist exchanges `δ` and `r`. -/
theorem theoremD_transport_eps_one {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    {w : ℕ} (κ : G →+ ZMod 2)
    (hw : ∀ c : ZMod 2, (Finset.univ.filter fun g : G => κ g = c).card = w)
    (E₁ : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ) (P₁ Q₁ : Matrix (Fin 4) (Fin 4) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G) (hρ : κ ρ = 0)
    (hE : ∀ r c, IsSign (E₁ r c)) (hP : ∀ r J, IsSign (P₁ r J)) (hQ : ∀ I c, IsSign (Q₁ I c))
    (hx : ∀ q g, IsSign (x q g))
    (hQgram : Q₁ * Q₁.transpose = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hprofile : ∀ t : G, t ≠ 0 → sumPaf x t = -4)
    (h3 : E₁ * E₁.transpose + (Fintype.card G : ℤ) • (P₁ * P₁.transpose)
      = (4 * ((Fintype.card G : ℤ) + 1)) • 1)
    (h4 : E₁ * Q₁.transpose + P₁ * (Lam (rvec x)).transpose = 0) :
    Matrix.IsHadamard (border κ E₁ (doubleRow P₁) (doubleCol Q₁) (seedTwist κ x) ρ) :=
  theoremD_transport κ hw E₁ P₁ Q₁ x ρ hE hP hQ hx hQgram hprofile h3 h4
    (dvec_seedTwist_of_eps_one κ x hρ)

/-! ### The converse of the transport -/

/-- **The converse of the transport clause of (D-e)** (`NOTE-B` §1.5).

The note's transport hypothesis `d = r` is not decoration and not a convenience: it is
*forced*.  If the doubled tables satisfy (H4) at `i = 2` then, by `theoremD_border`, the
transported system reads `P₁ Λ(d)ᵀ Q₁ = P₁ Λ(r)ᵀ Q₁`.  Cancelling the two `4 × 4`
Hadamard factors leaves `Λ(d) = Λ(r)`, and `Λ` is injective.

The cancellation stays in `ℤ`, where the note inverts `P₁` over `ℚ`: `Q₁ Q₁ᵀ = 4·I₄`
and `P₁ᵀ P₁ = 4·I₄` turn the equation into `16·Λ(d)ᵀ = 16·Λ(r)ᵀ`, and `ℤ` is
torsion free. -/
theorem theoremD_transport_converse {G : Type*} [Fintype G] [AddCommGroup G]
    (κ : G →+ ZMod 2)
    (E₁ : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ) (P₁ Q₁ : Matrix (Fin 4) (Fin 4) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G)
    (hP : ∀ r J, IsSign (P₁ r J)) (hQ : ∀ I c, IsSign (Q₁ I c))
    (hPgram : P₁ * P₁.transpose = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hQgram : Q₁ * Q₁.transpose = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (h4 : E₁ * Q₁.transpose + P₁ * (Lam (rvec x)).transpose = 0)
    (h4' : H4 (s := 1) E₁ (doubleRow P₁) (doubleCol Q₁) (chat κ (seedTwist κ x) ρ)) :
    dvec κ (seedTwist κ x) ρ = rvec x := by
  have hQhad : Matrix.IsHadamard Q₁ := by
    refine Matrix.IsHadamard.of_mul_conjTranspose
      (fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (hQ i j)) ?_ ?_
    · rw [Matrix.conjTranspose_eq_transpose_of_trivial, hQgram]
      norm_num
    · rw [isRegular_iff_ne_zero]
      norm_num
  have hPhad : Matrix.IsHadamard P₁ := by
    refine Matrix.IsHadamard.of_mul_conjTranspose
      (fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (hP i j)) ?_ ?_
    · rw [Matrix.conjTranspose_eq_transpose_of_trivial, hPgram]
      norm_num
    · rw [isRegular_iff_ne_zero]
      norm_num
  have hUTU : Q₁.transpose * Q₁ = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    have h := hQhad.conjTranspose_mul
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    simpa using h
  have hPTP : P₁.transpose * P₁ = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    have h := hPhad.conjTranspose_mul
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    simpa using h
  -- The two Hadamard factors cancel over `ℤ`: `4·A = 4·B` and `ℤ` is torsion free.
  have hcancelQ : ∀ A B : Matrix (Fin 4) (Fin 4) ℤ, A * Q₁ = B * Q₁ → A = B := by
    intro A B h
    have h' := congrArg (fun X : Matrix (Fin 4) (Fin 4) ℤ => X * Q₁.transpose) h
    simp only [Matrix.mul_assoc, hQgram, Matrix.mul_smul, Matrix.mul_one] at h'
    ext i j
    have hij := congrFun (congrFun h' i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    omega
  have hcancelP : ∀ A B : Matrix (Fin 4) (Fin 4) ℤ, P₁ * A = P₁ * B → A = B := by
    intro A B h
    have h' := congrArg (fun X : Matrix (Fin 4) (Fin 4) ℤ => P₁.transpose * X) h
    simp only [← Matrix.mul_assoc, hPTP, Matrix.smul_mul, Matrix.one_mul] at h'
    ext i j
    have hij := congrFun (congrFun h' i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    omega
  have hUeq : (Matrix.of fun I c : Fin 4 => doubleCol Q₁ (I, 0) c) = Q₁ := by
    ext I c
    exact doubleCol_zero Q₁ I c
  have hpeq : (Matrix.of fun r J : Fin 4 => doubleRow P₁ r (J, 0)) = P₁ := by
    ext r J
    exact doubleRow_zero P₁ r J
  -- The `i = 2` border equation, collapsed to `4·E₁ = −P₁ Λ(d)ᵀ Q₁`.
  have hbord := (theoremD_border κ (seedTwist κ x) ρ E₁ (doubleRow P₁) (doubleCol Q₁)
    (fun I => by funext c; simp only [Pi.neg_apply, doubleCol_one, doubleCol_zero])
    (fun r J => by rw [doubleRow_one, doubleRow_zero])
    (by rw [hUeq]; exact hQhad)).mp h4'
  rw [hUeq, hpeq] at hbord
  -- The `i = 1` border equation, multiplied through by `Q₁`.
  have h4Q : (4 : ℤ) • E₁ = -(P₁ * (Lam (rvec x)).transpose * Q₁) := by
    have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℤ => A * Q₁) h4
    simp only [Matrix.zero_mul] at h
    rw [Matrix.add_mul, Matrix.mul_assoc, hUTU, Matrix.mul_smul, Matrix.mul_one] at h
    rw [eq_neg_iff_add_eq_zero]
    exact h
  have hLam : (Lam (dvec κ (seedTwist κ x) ρ)).transpose = (Lam (rvec x)).transpose :=
    hcancelP _ _ (hcancelQ _ _ (neg_injective (hbord.symm.trans h4Q)))
  refine Lam_injective ?_
  have h := congrArg Matrix.transpose hLam
  simpa using h

/-- **The transport, as the note's "exactly when"** (`NOTE-B` §1.5, (D-e)).

Doubling an `i = 1` border and twisting the seeds produces a valid `i = 2` border
**if and only if** `d = r`.  `theoremD_transport` is the sufficiency half and
`theoremD_transport_converse` the necessity half; the `4 × 4` Gram `P₁ P₁ᵀ = 4·I₄` is
the one hypothesis the sufficiency half does not need. -/
theorem theoremD_transport_iff {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    {w : ℕ} (κ : G →+ ZMod 2)
    (hw : ∀ c : ZMod 2, (Finset.univ.filter fun g : G => κ g = c).card = w)
    (E₁ : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ) (P₁ Q₁ : Matrix (Fin 4) (Fin 4) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G)
    (hE : ∀ r c, IsSign (E₁ r c)) (hP : ∀ r J, IsSign (P₁ r J)) (hQ : ∀ I c, IsSign (Q₁ I c))
    (hx : ∀ q g, IsSign (x q g))
    (hPgram : P₁ * P₁.transpose = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hQgram : Q₁ * Q₁.transpose = (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hprofile : ∀ t : G, t ≠ 0 → sumPaf x t = -4)
    (h3 : E₁ * E₁.transpose + (Fintype.card G : ℤ) • (P₁ * P₁.transpose)
      = (4 * ((Fintype.card G : ℤ) + 1)) • 1)
    (h4 : E₁ * Q₁.transpose + P₁ * (Lam (rvec x)).transpose = 0) :
    Matrix.IsHadamard (border κ E₁ (doubleRow P₁) (doubleCol Q₁) (seedTwist κ x) ρ) ↔
      dvec κ (seedTwist κ x) ρ = rvec x := by
  constructor
  · intro hH
    -- Equal nonempty fibers make `κ` surjective, so Theorem A returns (H4) at `i = 2`.
    have hn : (Fintype.card G : ℤ) = 2 * (w : ℤ) := by
      have h := sum_comp_of_card_fiber_eq (⇑κ) hw fun _ => (1 : ℤ)
      rw [zmod2_sum] at h
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
      rw [h]
      ring
    have hn' : Fintype.card G = 2 * w := by exact_mod_cast hn
    have hpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨(0 : G)⟩
    have hsurj : Function.Surjective κ := by
      intro c
      have hne : (Finset.univ.filter fun g : G => κ g = c).Nonempty := by
        rw [← Finset.card_pos, hw c]
        omega
      obtain ⟨g, hg⟩ := hne
      exact ⟨g, (Finset.mem_filter.mp hg).2⟩
    obtain ⟨-, -, h4'⟩ := (theoremA (s := 1) (w := w) κ hsurj hw E₁ (doubleRow P₁)
      (doubleCol Q₁) (seedTwist κ x) ρ hE (fun r z => doubleRow_isSign hP r z)
      (fun z c => doubleCol_isSign hQ z c) ((seedTwist_isSign_iff κ x).mp hx)).mp hH
    exact theoremD_transport_converse κ E₁ P₁ Q₁ x ρ hP hQ hPgram hQgram h4 h4'
  · intro hd
    exact theoremD_transport κ hw E₁ P₁ Q₁ x ρ hE hP hQ hx hQgram hprofile h3 h4 hd

/-! ### The index-two collapse -/

/-- **The index-two collapse, seed-problem bijection** (`NOTE-B` §1.6,
Corollary — the seed-problem bijection clause).

The character twist `x ↦ ψ x` with `ψ(g) = (−1)^{κ g}` is

1. an **involution** of quadruples,
2. a bijection of **sign-valued** quadruples, and
3. a bijection from the `s = 1, i = 1` seed problem — the profile
   `Σ PAF(t) = −4` for `t ≠ 0` — onto the `s = 1, i = 2` seed problem, hypothesis
   (H2) of Theorem A for the house Gram table `houseM 1`.

So the two seed problems are one problem; any exhaustive statement proved on one
side transports to the other.

The bijection is of **seed problems, not of matrices**: it does not say the
assembled Hadamard matrices are equivalent (`NOTE-B` §3.4 proves they are not, at
order 668).  The `Aut G`-equivariance upgrade of `NOTE-B` §1.6 is
future work; see this file's module docstring. -/
theorem collapse_seedProblem_bijection {G : Type*} [AddCommGroup G] [Fintype G]
    (κ : G →+ ZMod 2) (x : Fin 4 → G → ℤ) :
    seedTwist κ (seedTwist κ x) = x ∧
      ((∀ q g, IsSign (x q g)) ↔ ∀ q g, IsSign (seedTwist κ x q g)) ∧
      ((∀ t : G, t ≠ 0 → sumPaf x t = -4) ↔ H2 (seedTwist κ x) κ (houseM 1)) := by
  refine ⟨seedTwist_seedTwist κ x, seedTwist_isSign_iff κ x, ?_⟩
  have hM : ∀ t : G, -houseM (Gbar := ZMod 2) 1 (κ t) = if κ t = 0 then (-4 : ℤ) else 4 := by
    intro t
    rcases zmod2_cases (κ t) with hk | hk
    · rw [if_pos hk, hk, houseM_zero]
      norm_num
    · rw [if_neg (by rw [hk]; decide), houseM_of_ne 1 (by rw [hk]; decide)]
      norm_num
  rw [show H2 (seedTwist κ x) κ (houseM 1) ↔
      ∀ t : G, t ≠ 0 → sumPaf (seedTwist κ x) t = if κ t = 0 then (-4 : ℤ) else 4 from
    ⟨fun h t ht => by rw [h t ht, hM t], fun h t ht => by rw [h t ht, ← hM t]⟩]
  exact twist_profile_iff (psi2 κ) (psi2_sq κ) κ (fun _ => rfl) x

end HadamardBFormalCore
