import Mathlib

/-!
# High-dimensional envy-free partitions

Authors: Pablo Soberon and Christina Yu.
Origin: [NYC Discrete Math REU 2023](https://geometrynyc.wixsite.com/home/previous-years).
Reference: P. Soberon and C. Yu, *High-dimensional envy-free partitions*, arXiv:2311.09905v1
(2023), 14 pp.
-/

namespace Soberon2023High

open MeasureTheory

/-- A convex partition: closed convex pieces covering the space with pairwise disjoint
interiors (p. 2). -/
def IsConvexPartition {d n : ℕ} (C : Fin n → Set (Fin d → ℝ)) : Prop :=
  (∀ i, IsClosed (C i) ∧ Convex ℝ (C i)) ∧
    (⋃ i, C i) = Set.univ ∧
    Pairwise (fun i j ↦ Disjoint (interior (C i)) (interior (C j)))

/-- An envy-free partition: a bijective allocation gives each measure a piece of maximal value
among all pieces (p. 2). -/
def IsEnvyFree {d n : ℕ} (C : Fin n → Set (Fin d → ℝ))
    (μ : Fin n → Measure (Fin d → ℝ)) : Prop :=
  ∃ π : Equiv.Perm (Fin n), ∀ i j, μ i (C j) ≤ μ i (C (π i))

/-- **Conjecture 5.1** (p. 12). Any `d` groups of `n` absolutely continuous probability measures
on real `d`-space admit one convex partition that is envy-free for every group. -/
theorem simultaneous_envy_free_convex_partition {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (μ : Fin d → Fin n → Measure (Fin d → ℝ))
    (hprob : ∀ r i, IsProbabilityMeasure (μ r i))
    (hac : ∀ r i, μ r i ≪ volume) :
    ∃ C : Fin n → Set (Fin d → ℝ), IsConvexPartition C ∧
      ∀ r, IsEnvyFree C (μ r) := by
  sorry

end Soberon2023High
