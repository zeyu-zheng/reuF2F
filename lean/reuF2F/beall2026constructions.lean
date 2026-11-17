import Mathlib

/-!
# Constructions of Macaulay Posets and Macaulay Rings

Authors: Penelope Beall, Erenay Boyali, Nancy Chen, Ellen Chlachidze, Trong Toan Dao,
Frederic Garvey, Mitchell Johnson, Yu Olivier Li, Nikola Kuzmanovski, Kelvin Ma, Treanungkur Mal,
Rukshan Marasinghe Mudiyanselage, Quinlan Mayo, Nava Minsky-Primus, Alexandra Seceleanu, and
Sriram Veerapaneni.
Origin: [Polymath Jr.](https://geometrynyc.wixsite.com/polymathreu).
Reference: P. Beall et al., *Constructions of Macaulay Posets and Macaulay Rings*,
arXiv:2502.15166.
-/

noncomputable section

namespace Beall2026Constructions

open Finset

section Posets

variable {α : Type*}

/-- A finite ranked poset: a least element of rank zero and covers that increase rank by one
(Section 2). -/
@[nolint unusedArguments]
def IsFiniteRankedPoset [PartialOrder α] [Fintype α] (rank : α → ℕ) : Prop :=
  ∃ least : α, rank least = 0 ∧ (∀ x : α, least ≤ x) ∧
    ∀ ⦃a b : α⦄, a ⋖ b → rank b = rank a + 1

/-- The rank-`d` level of a finite poset. -/
def level [Fintype α] (rank : α → ℕ) (d : ℕ) : Finset α :=
  {x | rank x = d}

open scoped Classical in
/-- The upper shadow (Section 2). It is defined using covers rather than all larger elements. -/
def upperShadow [PartialOrder α] [Fintype α] (A : Finset α) : Finset α :=
  {b | ∃ a ∈ A, a ⋖ b}

/-- A total order on each rank level. -/
structure LevelOrders (α : Type*) [Fintype α] [DecidableEq α] (rank : α → ℕ) where
  /-- The total order on each rank level. -/
  order : ∀ d : ℕ, LinearOrder {x : α // x ∈ level rank d}

/-- A size-`q` initial segment: the `q` largest elements of a level. -/
def IsInitialSegmentOfSize [Fintype α] [DecidableEq α] {rank : α → ℕ}
    (O : LevelOrders α rank) (d q : ℕ) (S : Finset α) : Prop :=
  S ⊆ level rank d ∧ #S = q ∧
    ∀ ⦃x y : α⦄, x ∈ S → ∀ (hx : x ∈ level rank d) (hy : y ∈ level rank d),
      (letI := O.order d;
        (⟨x, hx⟩ : {z : α // z ∈ level rank d}) ≤ ⟨y, hy⟩) → y ∈ S

/-- The Macaulay property: initial segments minimize upper shadows, and their upper shadows are
again initial segments (Section 2). -/
def IsMacaulayPoset [PartialOrder α] [Fintype α] [DecidableEq α] {rank : α → ℕ}
    (O : LevelOrders α rank) : Prop :=
  IsFiniteRankedPoset rank ∧
    ∀ (d : ℕ) (A : Finset α), A ⊆ level rank d →
      ∀ S : Finset α, IsInitialSegmentOfSize O d #A S →
        #(upperShadow S) ≤ #(upperShadow A) ∧
          IsInitialSegmentOfSize O (d + 1) #(upperShadow S) (upperShadow S)

end Posets

section Setup

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Nonzero monomials in the quotient, not exponent-vector representatives. Relations such as
`y ^ 2 = z ^ 2` thus identify monomials, as in the source examples. -/
abbrev QuotientMonomial {K : Type*} [Field K] {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) K)) :=
  {x : MvPolynomial (Fin m) K ⧸ I // x ≠ 0 ∧
    ∃ a : Fin m →₀ ℕ, Ideal.Quotient.mk I (MvPolynomial.monomial a (1 : K)) = x}

open scoped Classical in
/-- The finite Macaulay monomial poset of a homogeneous quotient. The order is certified as
multiplication by a monomial in the quotient, and the rank by every exponent representative. -/
def IsMacaulayQuotient {K : Type*} [Field K] {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) K) ∧
    ∃ (fin : Fintype (QuotientMonomial I)) (order : PartialOrder (QuotientMonomial I)),
      letI := fin;
      letI := order;
      (∀ a b : QuotientMonomial I, a ≤ b ↔
        ∃ c : Fin m →₀ ℕ,
          b.1 = a.1 * Ideal.Quotient.mk I (MvPolynomial.monomial c (1 : K))) ∧
        ∃ rank : QuotientMonomial I → ℕ,
          (∀ (a : QuotientMonomial I) (e : Fin m →₀ ℕ),
            Ideal.Quotient.mk I (MvPolynomial.monomial e (1 : K)) = a.1 →
              rank a = e.degree) ∧
          ∃ O : LevelOrders (QuotientMonomial I) rank, IsMacaulayPoset O

end Setup

/-- **Conjecture 7.4** (journal and arXiv v2; Conjecture 6.4 in v1). Tensoring a Macaulay ring
with `K[x] / (x ^ n)` preserves the Macaulay property when `n` exceeds its largest degree.

Macaulay means the monomial-poset property defined after Definition 2.12, not an unrestricted
Hilbert-function correspondence. -/
theorem conjecture_7_4
    {K : Type*} [Field K] {m : ℕ} (I : Ideal (MvPolynomial (Fin m) K))
    (hS : IsMacaulayQuotient I) (D n : ℕ)
    (hD : IsGreatest {d : ℕ | ∃ a : Fin m →₀ ℕ,
      MvPolynomial.monomial a (1 : K) ∉ I ∧ a.degree = d} D)
    (hn : D < n) :
    IsMacaulayQuotient
      (Ideal.map (MvPolynomial.rename (Fin.castSucc : Fin m → Fin (m + 1))) I ⊔
        Ideal.span ({MvPolynomial.X (Fin.last m) ^ n} : Set (MvPolynomial (Fin (m + 1)) K))) := by
  sorry

end Beall2026Constructions
