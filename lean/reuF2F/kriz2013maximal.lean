import Mathlib

/-!
# On the Maximal Cross Number of Unique Factorization Indexed Multisets

Author: Daniel Kriz.
Origin: [University of Minnesota Duluth REU 2012](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: D. Kriz, *On the maximal cross number of unique factorization indexed multisets*,
J. Number Theory **133** (2013), 3033-3056; arXiv:1301.1401.
-/

noncomputable section

universe u

namespace Kriz2013Maximal

/-- An indexed multiset over `G`: a finite index type whose indices carry values in `G`. -/
structure IndexedMultiset (G : Type u) where
  /-- The finite index type. -/
  ι : Type u
  instFintype : Fintype ι
  /-- The value in `G` carried by each index. -/
  elem : ι → G

namespace IndexedMultiset

attribute [instance] instFintype

variable {G : Type u}

/-- The restriction of an indexed multiset to the submultiset on a finite set of indices. -/
def restrict (S : IndexedMultiset G) (I : Finset S.ι) : IndexedMultiset G where
  ι := {i : S.ι // i ∈ I}
  instFintype := inferInstance
  elem := fun i ↦ S.elem i.1

/-- `S(I)` is a minimal zero-sum indexed submultiset. -/
def IsMinimalZeroSumOn [AddCommMonoid G] (S : IndexedMultiset G)
    (I : Finset S.ι) : Prop :=
  I.Nonempty ∧ (∑ i ∈ I, S.elem i) = 0 ∧
    ∀ J : Finset S.ι, J ⊂ I → J.Nonempty → (∑ i ∈ J, S.elem i) ≠ 0

/-- An irreducible factorization of `S`: a finite set of minimal zero-sum index blocks that
partitions the indexing set. -/
def IsIrreducibleFactorization [AddCommMonoid G] (S : IndexedMultiset G)
    (F : Finset (Finset S.ι)) : Prop :=
  (∀ I ∈ F, S.IsMinimalZeroSumOn I) ∧
    ∀ i : S.ι, ∃! I : Finset S.ι, I ∈ F ∧ i ∈ I

/-- A unique factorization indexed multiset (UFIM): a zero-sum indexed multiset
over `G \ {0}` with exactly one irreducible factorization, up to reordering of
the factor blocks. -/
def IsUFIM [AddCommMonoid G] (S : IndexedMultiset G) : Prop :=
  (∀ i : S.ι, S.elem i ≠ 0) ∧ (∑ i : S.ι, S.elem i) = 0 ∧
    ∃ F : Finset (Finset S.ι), S.IsIrreducibleFactorization F ∧
      ∀ E : Finset (Finset S.ι), S.IsIrreducibleFactorization E → E = F

/-- The cross number `k(S) = sum_{i in indices} 1 / ord(g_i)`. -/
def crossNumber [AddMonoid G] (S : IndexedMultiset G) : ℚ :=
  ∑ i : S.ι, (1 : ℚ) / (addOrderOf (S.elem i) : ℚ)

end IndexedMultiset

/-- `q` is Kriz's `K_1(G)`, the maximal cross number among UFIMs over
`G \ {0}`. -/
def HasMaximalUFIMCrossNumber (G : Type*) [AddCommGroup G] (q : ℚ) : Prop :=
  IsGreatest {r : ℚ | ∃ S : IndexedMultiset G,
    S.IsUFIM ∧ S.crossNumber = r} q

/-- **Conjecture 43**. A maximal-cross-number UFIM over a finite abelian group is a disjoint
union of UFIMs supported on its Sylow components. -/
theorem conjecture_maximal_ufim_splits_over_sylow_components
    {G : Type*} [AddCommGroup G] [Finite G]
    (S : IndexedMultiset G) (hS : S.IsUFIM)
    (hmax : HasMaximalUFIMCrossNumber G (S.crossNumber)) :
    ∃ parts : {p : ℕ // p ∈ (Nat.card G).primeFactors} → Finset S.ι,
      (∀ x : S.ι, ∃! p, x ∈ parts p) ∧
        ∀ p, (S.restrict (parts p)).IsUFIM ∧
          ∀ x ∈ parts p, S.elem x ∈ AddCommGroup.primaryComponent G p.1 := by
  sorry

end Kriz2013Maximal
