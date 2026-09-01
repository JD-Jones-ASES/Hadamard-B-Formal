import HadamardBFormal

/-!
# Bordered Goethals--Seidel arrays: the solution

This module exposes exactly the public challenge statements under the Palomar
namespace and discharges them through the internal, provenance-tracked
formalization in `HadamardBFormal/`.
-/

namespace HadamardBFormal

open scoped BigOperators Matrix

def IsSign (z : ℤ) : Prop :=
  z = 1 ∨ z = -1

def HadamardExists (n : ℕ) : Prop :=
  ∃ H : Matrix (Fin n) (Fin n) ℤ, H.IsHadamard

def dev {G : Type*} [Sub G] (x : G → ℤ) : Matrix G G ℤ :=
  fun g h => x (h - g)

def reflect {G : Type*} [AddCommGroup G] (ρ : G) : Equiv.Perm G :=
  Equiv.subLeft ρ

def revCols {G : Type*} (r : Equiv.Perm G) (A : Matrix G G ℤ) : Matrix G G ℤ :=
  fun g h => A g (r h)

def paf {G : Type*} [Fintype G] [Add G] (x : G → ℤ) (t : G) : ℤ :=
  ∑ u, x u * x (u + t)

def sumPaf {G : Type*} [Fintype G] [Add G] (x : Fin 4 → G → ℤ) (t : G) : ℤ :=
  ∑ q, paf (x q) t

def cosetSum {G Gbar : Type*} [Fintype G] [DecidableEq Gbar] (κ : G → Gbar) (x : G → ℤ)
    (c : Gbar) : ℤ :=
  ∑ g with κ g = c, x g

def gsBlock {G : Type*} (r : Equiv.Perm G) (X : Fin 4 → Matrix G G ℤ) :
    Fin 4 → Fin 4 → Matrix G G ℤ :=
  ![
    ![X 0, revCols r (X 1), revCols r (X 2), revCols r (X 3)],
    ![-revCols r (X 1), X 0, revCols r ((X 3).transpose), -revCols r ((X 2).transpose)],
    ![-revCols r (X 2), -revCols r ((X 3).transpose), X 0, revCols r ((X 1).transpose)],
    ![-revCols r (X 3), revCols r ((X 2).transpose), -revCols r ((X 1).transpose), X 0]
  ]

def gs {G : Type*} (r : Equiv.Perm G) (X : Fin 4 → Matrix G G ℤ) :
    Matrix (Fin 4 × G) (Fin 4 × G) ℤ :=
  fun i j => gsBlock r X i.1 j.1 i.2 j.2

def core {G : Type*} [AddCommGroup G] (x : Fin 4 → G → ℤ) (ρ : G) :
    Matrix (Fin 4 × G) (Fin 4 × G) ℤ :=
  gs (reflect ρ) fun q => dev (x q)

def rowStrip {G Gbar : Type*} {s : ℕ} (κ : G → Gbar)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ) :
    Matrix (Fin (4 * s)) (Fin 4 × G) ℤ :=
  fun r z => P r (z.1, κ z.2)

def colStrip {G Gbar : Type*} {s : ℕ} (κ : G → Gbar)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ) :
    Matrix (Fin 4 × G) (Fin (4 * s)) ℤ :=
  fun z c => Q (z.1, κ z.2) c

def chat {G Gbar : Type*} [Fintype G] [AddCommGroup G] [AddCommGroup Gbar] [DecidableEq Gbar]
    (κ : G →+ Gbar) (x : Fin 4 → G → ℤ) (ρ : G) : Matrix (Fin 4 × Gbar) (Fin 4 × Gbar) ℤ :=
  core (fun q => cosetSum κ (x q)) (κ ρ)

def border {G Gbar : Type*} [AddCommGroup G] [AddCommGroup Gbar] {s : ℕ} (κ : G →+ Gbar)
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G) :
    Matrix (Fin (4 * s) ⊕ (Fin 4 × G)) (Fin (4 * s) ⊕ (Fin 4 × G)) ℤ :=
  Matrix.fromBlocks E (rowStrip κ P) (colStrip κ Q) (core x ρ)

def H1 {Gbar : Type*} {s : ℕ} [AddCommGroup Gbar] (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (M : Gbar → ℤ) : Prop :=
  ∀ a b : Fin 4 × Gbar, (∑ c, Q a c * Q b c) = if a.1 = b.1 then M (a.2 - b.2) else 0

def H2 {G Gbar : Type*} [Fintype G] [AddCommGroup G] [AddCommGroup Gbar] (x : Fin 4 → G → ℤ)
    (κ : G →+ Gbar) (M : Gbar → ℤ) : Prop :=
  ∀ t : G, t ≠ 0 → sumPaf x t = -M (κ t)

def H3 {Gbar : Type*} {s : ℕ} [Fintype Gbar] [DecidableEq Gbar]
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ) (w N : ℤ) : Prop :=
  E * E.transpose + w • (P * P.transpose) = N • 1

def H4 {Gbar : Type*} {s : ℕ} [Fintype Gbar] [DecidableEq Gbar]
    (E : Matrix (Fin (4 * s)) (Fin (4 * s)) ℤ)
    (P : Matrix (Fin (4 * s)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * s)) ℤ)
    (Chat : Matrix (Fin 4 × Gbar) (Fin 4 × Gbar) ℤ) : Prop :=
  E * Q.transpose + P * Chat.transpose = 0

def houseM {Gbar : Type*} [Zero Gbar] [DecidableEq Gbar] (s : ℕ) : Gbar → ℤ :=
  fun e => if e = 0 then 4 * (s : ℤ) else -4

def twistDiagBar {Gbar : Type*} [DecidableEq Gbar] (ψbar : Gbar → ℤ) :
    Matrix (Fin 4 × Gbar) (Fin 4 × Gbar) ℤ :=
  Matrix.diagonal fun z : Fin 4 × Gbar => ψbar z.2

def twistConj {G : Type*} [AddCommGroup G] [DecidableEq G] (s : ℕ) (ψ : AddChar G ℤ) :
    Matrix (Fin (4 * s) ⊕ (Fin 4 × G)) (Fin (4 * s) ⊕ (Fin 4 × G)) ℤ :=
  Matrix.fromBlocks 1 0 0 (Matrix.diagonal fun z : Fin 4 × G => ψ z.2)

def Lam (y : Fin 4 → ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ y 0,  y 1,  y 2,  y 3;
     -y 1,  y 0,  y 3, -y 2;
     -y 2, -y 3,  y 0,  y 1;
     -y 3,  y 2, -y 1,  y 0]

def eps {G : Type*} [AddCommGroup G] (κ : G →+ ZMod 2) (ρ : G) : ℤ :=
  if κ ρ = 0 then 1 else -1

def delta {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2) (x : G → ℤ) : ℤ :=
  cosetSum κ x 0 - cosetSum κ x 1

def dvec {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2) (x : Fin 4 → G → ℤ) (ρ : G) :
    Fin 4 → ℤ :=
  ![delta κ (x 0), eps κ ρ * delta κ (x 1), eps κ ρ * delta κ (x 2), eps κ ρ * delta κ (x 3)]

def psi2 {G : Type*} [AddCommGroup G] (κ : G →+ ZMod 2) : AddChar G ℤ where
  toFun g := if κ g = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro a b
    have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hcases (κ a) with ha | ha <;> rcases hcases (κ b) with hb | hb <;>
      simp only [map_add, ha, hb] <;> decide

def rvec {G : Type*} [Fintype G] (x : Fin 4 → G → ℤ) : Fin 4 → ℤ :=
  fun q => ∑ g, x q g

def seedTwist {G : Type*} [AddCommGroup G] (κ : G →+ ZMod 2) (x : Fin 4 → G → ℤ) :
    Fin 4 → G → ℤ :=
  fun q g => psi2 κ g * x q g

def doubleRow (P : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ :=
  fun r z => if z.2 = 0 then P r z.1 else -P r z.1

def doubleCol (Q : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin 4 × ZMod 2) (Fin (4 * 1)) ℤ :=
  fun z c => if z.2 = 0 then Q z.1 c else -Q z.1 c

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
    Matrix.IsHadamard (border κ E P Q x ρ) :=
  HadamardBFormalCore.theoremA_sufficiency κ hw E P Q x ρ hE hP hQ hx M h1 h2 h3 h4

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
        ∧ H4 E P Q (chat κ x ρ) :=
  HadamardBFormalCore.theoremA κ hκ hw E P Q x ρ hE hP hQ hx

theorem theoremB_profile {G Gbar : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    [AddCommGroup Gbar] [DecidableEq Gbar] (x : Fin 4 → G → ℤ) (hx : ∀ q g, IsSign (x q g))
    (κ : G →+ Gbar) (s : ℕ) :
    H2 x κ (houseM s) ↔
      ∀ t : G, sumPaf x t
        = 4 * (Fintype.card G : ℤ) * (if t = 0 then 1 else 0)
          - 4 * (s : ℤ) * (if t ≠ 0 ∧ κ t = 0 then 1 else 0)
          + 4 * (if κ t ≠ 0 then 1 else 0) :=
  HadamardBFormalCore.theoremB_profile x hx κ s

theorem goethalsSeidel_abelian {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    [Nonempty G] (x : Fin 4 → G → ℤ) (ρ : G) (hx : ∀ q g, IsSign (x q g))
    (hprofile : ∀ t : G, sumPaf x t = 4 * (Fintype.card G : ℤ) * (if t = 0 then 1 else 0)) :
    Matrix.IsHadamard (core x ρ) :=
  HadamardBFormalCore.goethalsSeidel_abelian x ρ hx hprofile

theorem borderedGS_index_one {G Gbar : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup Gbar] [Fintype Gbar] [DecidableEq Gbar] [Subsingleton Gbar]
    (κ : G →+ Gbar)
    (E : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ)
    (P : Matrix (Fin (4 * 1)) (Fin 4 × Gbar) ℤ)
    (Q : Matrix (Fin 4 × Gbar) (Fin (4 * 1)) ℤ)
    (x : Fin 4 → G → ℤ) (ρ : G)
    (hE : ∀ r c, IsSign (E r c)) (hP : ∀ r z, IsSign (P r z))
    (hQ : ∀ z c, IsSign (Q z c)) (hx : ∀ q g, IsSign (x q g))
    (h1 : ∀ a b : Fin 4 × Gbar, (∑ c, Q a c * Q b c) = if a.1 = b.1 then 4 else 0)
    (h2 : ∀ t : G, t ≠ 0 → sumPaf x t = -4)
    (h3 : E * E.transpose + (Fintype.card G : ℤ) • (P * P.transpose)
      = (4 * ((Fintype.card G : ℤ) + 1)) • 1)
    (h4 : E * Q.transpose + P * (chat κ x ρ).transpose = 0) :
    Matrix.IsHadamard (border κ E P Q x ρ) :=
  HadamardBFormalCore.borderedGS_index_one κ E P Q x ρ hE hP hQ hx h1 h2 h3 h4

theorem D5 {G Gbar : Type*} [Fintype G] [AddCommGroup G]
    [AddCommGroup Gbar] [DecidableEq Gbar] {s w : ℕ} (κ : G →+ Gbar)
    (hw : ∀ c : Gbar, (Finset.univ.filter fun g : G => κ g = c).card = w)
    (x : Fin 4 → G → ℤ) (hx : ∀ q g, IsSign (x q g)) (h2 : H2 x κ (houseM s)) :
    (∑ q, (∑ g, x q g) ^ 2)
      = 8 * (Fintype.card G : ℤ) - 4 * (w : ℤ) * ((s : ℤ) + 1) + 4 * (s : ℤ) :=
  HadamardBFormalCore.D5 κ hw x hx h2

theorem D6 {G Gbar : Type*} [Fintype G] [AddCommGroup G]
    [AddCommGroup Gbar] [DecidableEq Gbar] [Subsingleton Gbar] {s : ℕ} (κ : G →+ Gbar)
    (x : Fin 4 → G → ℤ) (hx : ∀ q g, IsSign (x q g)) (h2 : H2 x κ (houseM s)) :
    (Fintype.card G : ℤ) * ((s : ℤ) - 1) ≤ (s : ℤ) :=
  HadamardBFormalCore.D6 κ x hx h2

theorem lemmaT {G : Type*} [AddCommGroup G] [Fintype G] (ψ : AddChar G ℤ)
    (hsq : ∀ g : G, ψ g * ψ g = 1) (x : G → ℤ) (t : G) :
    paf (fun g => ψ g * x g) t = ψ t * paf x t :=
  HadamardBFormalCore.lemmaT ψ hsq x t

theorem twist_profile_iff {G : Type*} [AddCommGroup G] [Fintype G] (ψ : AddChar G ℤ)
    (hsq : ∀ g : G, ψ g * ψ g = 1) (κ : G →+ ZMod 2)
    (hψ : ∀ g : G, ψ g = if κ g = 0 then 1 else -1) (x : Fin 4 → G → ℤ) :
    (∀ t : G, t ≠ 0 → sumPaf x t = -4) ↔
      ∀ t : G, t ≠ 0 → sumPaf (fun q g => ψ g * x q g) t = if κ t = 0 then -4 else 4 :=
  HadamardBFormalCore.twist_profile_iff ψ hsq κ hψ x

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
      twistConj s ψ * border κ E P Q x ρ * twistConj s ψ :=
  HadamardBFormalCore.twist_isConjugation κ ψ hsq ψbar hfac ρ hρ E P Q x

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
      Matrix.IsHadamard (border κ E P Q x ρ) :=
  HadamardBFormalCore.twist_isHadamard_iff κ ψ hsq ψbar hfac ρ hρ E P Q x

theorem deltaSqSum_eq_four {G : Type*} [Fintype G] [AddCommGroup G]
    (κ : G →+ ZMod 2) (x : Fin 4 → G → ℤ) (hx : ∀ q g, IsSign (x q g))
    (h2 : H2 x κ (houseM 1)) :
    (∑ q, delta κ (x q) ^ 2) = 4 :=
  HadamardBFormalCore.deltaSqSum_eq_four κ x hx h2

theorem theoremD_tables (Q : Matrix (Fin 4 × ZMod 2) (Fin 4) ℤ) (hQ : ∀ z c, IsSign (Q z c))
    (M : ZMod 2 → ℤ) (h1 : H1 (s := 1) Q M) :
    M 0 = 4 ∧ (M 1 = 4 ∨ M 1 = -4) ∧
      (M 1 = -4 →
        (∀ I : Fin 4, Q (I, 1) = -Q (I, 0)) ∧
          Matrix.IsHadamard (Matrix.of fun I c : Fin 4 => Q (I, 0) c)) :=
  HadamardBFormalCore.theoremD_tables Q hQ M h1

theorem theoremD_rowTable {G : Type*} [Fintype G] [AddCommGroup G] {w : ℕ}
    (κ : G →+ ZMod 2)
    (hw : ∀ c : ZMod 2, (Finset.univ.filter fun g : G => κ g = c).card = w) (hw2 : 2 ≤ w)
    (E : Matrix (Fin 4) (Fin 4) ℤ) (P : Matrix (Fin 4) (Fin 4 × ZMod 2) ℤ)
    (Q : Matrix (Fin 4 × ZMod 2) (Fin 4) ℤ) (x : Fin 4 → G → ℤ) (ρ : G)
    (hE : ∀ r c, IsSign (E r c)) (hP : ∀ r z, IsSign (P r z)) (hx : ∀ q g, IsSign (x q g))
    (h2 : H2 x κ (houseM 1))
    (h3 : H3 (s := 1) E P (w : ℤ) (4 * ((Fintype.card G : ℤ) + 1)))
    (h4 : H4 (s := 1) E P Q (chat κ x ρ))
    (hQpair : ∀ I : Fin 4, Q (I, 1) = -Q (I, 0)) :
    (∀ r J : Fin 4, P r (J, 1) = -P r (J, 0)) ∧
      Matrix.IsHadamard (Matrix.of fun r J : Fin 4 => P r (J, 0)) ∧
      Matrix.IsHadamard E :=
  HadamardBFormalCore.theoremD_rowTable κ hw hw2 E P Q x ρ hE hP hx h2 h3 h4 hQpair

theorem theoremD_border {G : Type*} [Fintype G] [AddCommGroup G] (κ : G →+ ZMod 2)
    (x : Fin 4 → G → ℤ) (ρ : G)
    (E : Matrix (Fin 4) (Fin 4) ℤ) (P : Matrix (Fin 4) (Fin 4 × ZMod 2) ℤ)
    (Q : Matrix (Fin 4 × ZMod 2) (Fin 4) ℤ)
    (hQpair : ∀ I : Fin 4, Q (I, 1) = -Q (I, 0))
    (hPpair : ∀ r J : Fin 4, P r (J, 1) = -P r (J, 0))
    (hU : Matrix.IsHadamard (Matrix.of fun I c : Fin 4 => Q (I, 0) c)) :
    H4 (s := 1) E P Q (chat κ x ρ) ↔
      (4 : ℤ) • E = -((Matrix.of fun r J : Fin 4 => P r (J, 0))
        * (Lam (dvec κ x ρ)).transpose * (Matrix.of fun I c : Fin 4 => Q (I, 0) c)) :=
  HadamardBFormalCore.theoremD_border κ x ρ E P Q hQpair hPpair hU

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
    Matrix.IsHadamard (border κ E₁ (doubleRow P₁) (doubleCol Q₁) (seedTwist κ x) ρ) :=
  HadamardBFormalCore.theoremD_transport κ hw E₁ P₁ Q₁ x ρ hE hP hQ hx hQgram hprofile h3 h4 hd

theorem collapse_seedProblem_bijection {G : Type*} [AddCommGroup G] [Fintype G]
    (κ : G →+ ZMod 2) (x : Fin 4 → G → ℤ) :
    seedTwist κ (seedTwist κ x) = x ∧
      ((∀ q g, IsSign (x q g)) ↔ ∀ q g, IsSign (seedTwist κ x q g)) ∧
      ((∀ t : G, t ≠ 0 → sumPaf x t = -4) ↔ H2 (seedTwist κ x) κ (houseM 1)) :=
  HadamardBFormalCore.collapse_seedProblem_bijection κ x

abbrev G52 : Type := ZMod 2 × ZMod 2 × ZMod 3

def gidx52 (z : G52) : Fin 12 :=
  ⟨6 * z.1.val + 3 * z.2.1.val + z.2.2.val, by
    have h0 : z.1.val < 2 := ZMod.val_lt z.1
    have h1 : z.2.1.val < 2 := ZMod.val_lt z.2.1
    have h2 : z.2.2.val < 3 := ZMod.val_lt z.2.2
    omega⟩

def pairIdx (z : Fin 4 × ZMod 2) : Fin 8 :=
  ⟨2 * z.1.val + z.2.val, by
    have h0 : z.1.val < 4 := z.1.isLt
    have h1 : z.2.val < 2 := ZMod.val_lt z.2
    omega⟩

def kappa52 : G52 →+ ZMod 2 where
  toFun z := z.1
  map_zero' := rfl
  map_add' _ _ := rfl

def rho52 : G52 := 0

def seed52Data : Vector (Vector Int 12) 4 :=
  #v[
    #v[
      -1, -1, 1, 1, 1, -1, -1, 1, -1, 1, -1, -1
    ],
    #v[
      -1, -1, 1, -1, -1, 1, 1, 1, -1, -1, -1, -1
    ],
    #v[
      1, -1, -1, 1, -1, -1, 1, 1, -1, -1, -1, -1
    ],
    #v[
      -1, 1, -1, 1, -1, -1, 1, 1, -1, -1, -1, -1
    ]
  ]

def seed52 : Fin 4 → G52 → ℤ := fun q g => (seed52Data.get q).get (gidx52 g)

def corner52Data : Vector (Vector Int 4) 4 :=
  #v[
    #v[
      -1, -1, -1, 1
    ],
    #v[
      -1, -1, 1, -1
    ],
    #v[
      -1, 1, -1, -1
    ],
    #v[
      1, -1, -1, -1
    ]
  ]

def E52 : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ :=
  fun r c => (corner52Data.get r).get c

def rowTable52Data : Vector (Vector Int 8) 4 :=
  #v[
    #v[
      -1, 1, 1, -1, 1, -1, -1, 1
    ],
    #v[
      1, -1, -1, 1, 1, -1, -1, 1
    ],
    #v[
      1, -1, 1, -1, -1, 1, -1, 1
    ],
    #v[
      -1, 1, -1, 1, -1, 1, -1, 1
    ]
  ]

def P52 : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ :=
  fun r z => (rowTable52Data.get r).get (pairIdx z)

def colTable52Data : Vector (Vector Int 8) 4 :=
  #v[
    #v[
      1, -1, 1, -1, 1, -1, -1, 1
    ],
    #v[
      -1, 1, -1, 1, 1, -1, -1, 1
    ],
    #v[
      -1, 1, 1, -1, -1, 1, -1, 1
    ],
    #v[
      1, -1, -1, 1, -1, 1, -1, 1
    ]
  ]

def Q52 : Matrix (Fin 4 × ZMod 2) (Fin (4 * 1)) ℤ :=
  fun z c => (colTable52Data.get c).get (pairIdx z)

abbrev G20 : Type := ZMod 2 × ZMod 2

def gidx20 (z : G20) : Fin 4 :=
  ⟨2 * z.1.val + z.2.val, by
    have h0 : z.1.val < 2 := ZMod.val_lt z.1
    have h1 : z.2.val < 2 := ZMod.val_lt z.2
    omega⟩

def kappa20 : G20 →+ ZMod 2 where
  toFun z := z.1 + z.2
  map_zero' := rfl
  map_add' a b := add_add_add_comm a.1 b.1 a.2 b.2

def rho20 : G20 := (1, 1)

def seed20Data : Vector (Vector Int 4) 4 :=
  #v[
    #v[
      -1, -1, 1, 1
    ],
    #v[
      -1, 1, -1, 1
    ],
    #v[
      1, -1, -1, -1
    ],
    #v[
      -1, -1, -1, -1
    ]
  ]

def seed20 : Fin 4 → G20 → ℤ := fun q g => (seed20Data.get q).get (gidx20 g)

def corner20Data : Vector (Vector Int 4) 4 :=
  #v[
    #v[
      -1, -1, -1, -1
    ],
    #v[
      1, 1, -1, -1
    ],
    #v[
      1, -1, 1, -1
    ],
    #v[
      -1, 1, 1, -1
    ]
  ]

def E20 : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ :=
  fun r c => (corner20Data.get r).get c

def rowTable20Data : Vector (Vector Int 8) 4 :=
  #v[
    #v[
      -1, 1, 1, -1, -1, 1, 1, -1
    ],
    #v[
      1, -1, 1, -1, -1, 1, -1, 1
    ],
    #v[
      1, -1, -1, 1, -1, 1, 1, -1
    ],
    #v[
      1, -1, 1, -1, 1, -1, 1, -1
    ]
  ]

def P20 : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ :=
  fun r z => (rowTable20Data.get r).get (pairIdx z)

def colRows20Data : Vector (Vector Int 4) 8 :=
  #v[
    #v[
      1, -1, -1, -1
    ],
    #v[
      -1, 1, 1, 1
    ],
    #v[
      -1, -1, 1, -1
    ],
    #v[
      1, 1, -1, 1
    ],
    #v[
      1, 1, 1, -1
    ],
    #v[
      -1, -1, -1, 1
    ],
    #v[
      1, -1, 1, 1
    ],
    #v[
      -1, 1, -1, -1
    ]
  ]

def Q20 : Matrix (Fin 4 × ZMod 2) (Fin (4 * 1)) ℤ :=
  fun z c => (colRows20Data.get (pairIdx z)).get c

theorem hadamard_52_bordered :
    Matrix.IsHadamard (border kappa52 E52 P52 Q52 seed52 rho52) :=
  HadamardBFormalCore.Data.hadamard_52_bordered

theorem gate52_columnTable :
    (∀ I : Fin 4, Q52 (I, 1) = -Q52 (I, 0)) ∧
      Matrix.IsHadamard (Matrix.of fun I c : Fin 4 => Q52 (I, 0) c) :=
  HadamardBFormalCore.Data.gate52_columnTable

theorem hadamardExists_52 : HadamardExists 52 :=
  HadamardBFormalCore.Data.hadamardExists_52

theorem hadamard_20_bordered :
    Matrix.IsHadamard (border kappa20 E20 P20 Q20 seed20 rho20) :=
  HadamardBFormalCore.Data.hadamard_20_bordered

theorem hadamardExists_20 : HadamardExists 20 :=
  HadamardBFormalCore.Data.hadamardExists_20

end HadamardBFormal
