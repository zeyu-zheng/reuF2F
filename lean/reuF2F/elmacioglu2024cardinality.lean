import Mathlib

/-!
# On the cardinality of minimal presentations of numerical semigroups

Authors: Ceyhun Elmacioglu, Kieran Hilmer, Christopher O'Neill, Melin Okandan,
and Hannah Park-Kaufmann.
Origin: [Polymath Jr. 2021](https://geometrynyc.wixsite.com/polymathreu).
Reference: C. Elmacioglu, K. Hilmer, C. O'Neill, M. Okandan, and H. Park-Kaufmann, *On the
cardinality of minimal presentations of numerical semigroups*, arXiv:2211.16283.
-/

noncomputable section

namespace Elmacioglu2024Cardinality

/-- A numerical monoid, given by its positive minimal generators. -/
structure NumericalMonoid where
  /-- The embedding dimension, the number of minimal generators. -/
  embDim : ℕ
  /-- The minimal generators, in increasing order. -/
  gen : Fin embDim → ℕ
  positive_gen : ∀ i : Fin embDim, 0 < gen i
  strictMono_gen : StrictMono gen
  irreducible_gen : ∀ i : Fin embDim, ∀ a b : ℕ,
    a ∈ AddSubmonoid.closure (Set.range gen) →
      b ∈ AddSubmonoid.closure (Set.range gen) →
        gen i = a + b → a = 0 ∨ b = 0
  minimal_gen : ∀ i : Fin embDim,
    gen i ∉ AddSubmonoid.closure {m : ℕ | ∃ j : Fin embDim, j ≠ i ∧ gen j = m}
  cofinite : Set.Finite {n : ℕ | n ∉ AddSubmonoid.closure (Set.range gen)}

namespace NumericalMonoid

/-- The least generator `n₁` in the paper's one-indexed notation. -/
def leastGenerator (Γ : NumericalMonoid) : ℕ :=
  if h : 0 < Γ.embDim then Γ.gen ⟨0, h⟩ else 0

/-- The factorization homomorphism `φ : ℕ^e → S`, evaluated as a natural number through the
chosen generators of `S`. -/
def factorizationValue (S : NumericalMonoid)
    (a : Fin S.embDim → ℕ) : ℕ :=
  ∑ i : Fin S.embDim, a i * S.gen i

/-- A trade (relation): a pair of factorizations of a numerical monoid. -/
abbrev Trade (S : NumericalMonoid) := (Fin S.embDim → ℕ) × (Fin S.embDim → ℕ)

/-- A presentation: all listed trades preserve the factorization homomorphism, and the
congruence they generate is exactly its kernel congruence. -/
def IsPresentation (S : NumericalMonoid) (ρ : Set (Trade S)) : Prop :=
  (∀ r ∈ ρ,
    factorizationValue S r.1 =
      factorizationValue S r.2) ∧
  ∀ a b : Fin S.embDim → ℕ,
    factorizationValue S a =
        factorizationValue S b ↔
      addConGen (fun x y ↦ (x, y) ∈ ρ) a b

/-- A minimal presentation: no proper subset remains a presentation. -/
def IsMinimalPresentation (S : NumericalMonoid) (ρ : Set (Trade S)) : Prop :=
  IsPresentation S ρ ∧ ∀ τ : Set (Trade S), τ ⊂ ρ → ¬IsPresentation S τ

/-- The invariant `η(S)`: every minimal presentation has cardinality `η`. -/
def MinimalPresentationCardinality (S : NumericalMonoid) (η : ℕ) : Prop :=
  (∃ ρ : Set (Trade S), ρ.Finite ∧ IsMinimalPresentation S ρ ∧ ρ.ncard = η) ∧
    ∀ ρ : Set (Trade S), ρ.Finite → IsMinimalPresentation S ρ → ρ.ncard = η

end NumericalMonoid

open NumericalMonoid

/-- **Conjecture 7.1**. For embedding dimension `4`, the families from Theorems 4.2 and 6.3 and
Proposition 6.2 attain all possible values of `η` for each multiplicity `m ≥ 4`. -/
theorem conjecture_7_1_embedding_dimension_four_families_complete
    (m η : ℕ) (hm : 4 ≤ m)
    (h : ∃ S : NumericalMonoid, S.embDim = 4 ∧ S.leastGenerator = m ∧
      NumericalMonoid.MinimalPresentationCardinality S η) :
    (∃ r s : ℕ, m = r + 4 ∧ s ≤ Nat.min (4 - 2) r ∧ η = Nat.choose 4 2 - s) ∨
      (8 ≤ m ∧ η = 3) ∨
        (6 ≤ η ∧ (η - 2) ^ 2 ≤ 4 * m) := by
  sorry

end Elmacioglu2024Cardinality
