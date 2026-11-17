import Mathlib

/-!
# An intermediate case of exponential multivalued forbidden matrix configurations

Authors: Wallace Peaslee, Attila Sali, and Jun Yan.
Origin: [Budapest Semesters in Mathematics 2020](https://www.bsmath.hu/articles.html).
Reference: W. Peaslee, A. Sali, and J. Yan, *An intermediate case of exponential multivalued
forbidden matrix configurations*, Art Discrete Appl. Math. (2026), accepted manuscript;
doi:10.26493/2590-9770.1898.8b5; arXiv:2312.11446 (2023).
-/

noncomputable section

namespace Peaslee2026Intermediate

open Filter
open scoped Topology
open Finset

/-- The choices of a triangular choice multigraph on `V`: each unordered triple chooses one of
its three pairs (Definition 1.3). Values off triples are ignored, and distinct triples may
choose the same pair. -/
def IsTriangularChoice {m : ℕ} (V : Finset (Fin m))
    (choose : Finset (Fin m) → Finset (Fin m)) : Prop :=
  ∀ t ∈ V.powersetCard 3, choose t ∈ t.powersetCard 2

/-- Recursive realizations of a TCM by splitting into two nonempty parts, where every mixed
triple chooses the pair in its two-vertex part (Definition 1.3). -/
inductive IsTwoRecursive {m : ℕ} (choose : Finset (Fin m) → Finset (Fin m)) :
    Finset (Fin m) → Prop
  | base {V : Finset (Fin m)} (hV : #V = 1 ∨ #V = 2) :
      IsTwoRecursive choose V
  | split {V₁ V₂ : Finset (Fin m)}
      (h₁ : V₁.Nonempty) (h₂ : V₂.Nonempty) (hd : Disjoint V₁ V₂)
      (hcard : 3 ≤ #(V₁ ∪ V₂))
      (r₁ : IsTwoRecursive choose V₁) (r₂ : IsTwoRecursive choose V₂)
      (mixed : ∀ t ∈ (V₁ ∪ V₂).powersetCard 3, ¬t ⊆ V₁ → ¬t ⊆ V₂ →
        choose t = if #(t ∩ V₁) = 2 then t ∩ V₁ else t ∩ V₂) :
      IsTwoRecursive choose (V₁ ∪ V₂)

/-- The number `m_G(e)` of triples that choose the unordered pair `e` (Question 1.4). -/
def multiplicity {m : ℕ} (V : Finset (Fin m))
    (choose : Finset (Fin m) → Finset (Fin m)) (e : Finset (Fin m)) : ℕ :=
  #{t ∈ V.powersetCard 3 | choose t = e}

/-- The weight `w(G, α)`, a sum over all unordered pairs (Question 1.4). Pairs of multiplicity
zero are included and contribute `α ^ 0 = 1`. -/
def weight {m : ℕ} (V : Finset (Fin m))
    (choose : Finset (Fin m) → Finset (Fin m)) (α : ℝ) : ℝ :=
  ∑ e ∈ V.powersetCard 2, α ^ multiplicity V choose e

/-- The maximum weight `H(m, α)` over all TCM realizations on `m` vertices (Question 1.4).
The set of choices is finite, so the supremum is a maximum. -/
def H (m : ℕ) (α : ℝ) : ℝ :=
  sSup {w : ℝ | ∃ choose : Finset (Fin m) → Finset (Fin m),
    IsTriangularChoice Finset.univ choose ∧ weight Finset.univ choose α = w}

/-- The maximum weight `H₂(m, α)` over recursively realized TCMs (Question 1.4). -/
def H₂ (m : ℕ) (α : ℝ) : ℝ :=
  sSup {w : ℝ | ∃ choose : Finset (Fin m) → Finset (Fin m),
    IsTriangularChoice Finset.univ choose ∧ IsTwoRecursive choose Finset.univ ∧
      weight Finset.univ choose α = w}

/-- The series `λ(α)` (before Theorem 1.8; Section 5.1). The source index `j ≥ 1` is shifted
to `j + 1`. -/
def lambda (α : ℝ) : ℝ :=
  ∑' j : ℕ, (2 : ℝ) ^ j / α ^ (2 ^ (j + 1))

/-- **Conjecture 6.3**. For every `α ≥ 2`, all TCMs and 2-recursive TCMs have the same maximum
weight for every `m ≥ 3`, and both normalized maxima converge to `λ(α)`.

The recursive class is that of Definition 1.3, not the exceptional-split formula of
Theorem 6.2. -/
theorem conjecture_6_3 (α : ℝ) (hα : 2 ≤ α) :
    (∀ m ≥ 3, H m α = H₂ m α) ∧
    Tendsto (fun m : ℕ ↦ 2 * H m α / ((m : ℝ) * α ^ m)) atTop (𝓝 (lambda α)) ∧
    Tendsto (fun m : ℕ ↦ 2 * H₂ m α / ((m : ℝ) * α ^ m)) atTop (𝓝 (lambda α)) := by
  sorry

end Peaslee2026Intermediate
