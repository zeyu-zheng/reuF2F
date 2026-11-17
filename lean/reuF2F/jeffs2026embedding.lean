import Mathlib

/-!
# Embedding dimension gaps in sparse codes

Authors: R. Amzi Jeffs, Henry Siegel, David Staudinger, and Yiqing Wang.
Origin: [Carnegie Mellon University SEMS
2023](https://www.cmu.edu/mcs/news-events/2023/1018-sems-program).
Reference: R. A. Jeffs, H. Siegel, D. Staudinger, and Y. Wang, *Embedding dimension gaps in
sparse codes*, Involve **19** (2026), 405-422; arXiv:2309.14862.
-/

namespace Jeffs2026Embedding

open Finset

/-- A Steiner triple system: triples such that each pair of distinct indices lies in exactly
one triple (Section 7). -/
structure SteinerTripleSystem (n : ℕ) where
  /-- The triples of the system. -/
  blocks : Finset (Finset (Fin n))
  triple_card : ∀ b ∈ blocks, #b = 3
  pair_unique : ∀ i j : Fin n, i ≠ j → ∃! b, b ∈ blocks ∧ i ∈ b ∧ j ∈ b

/-- The least dimension of a realization by bounded open convex sets, or `⊤` if none exists
(Section 1). -/
noncomputable def openEmbeddingDimension {n : ℕ} (C : Finset (Finset (Fin n))) : ℕ∞ :=
  sInf {m | ∃ d : ℕ, m = (d : ℕ∞) ∧
    ∃ U : Fin n → Set (EuclideanSpace ℝ (Fin d)),
      (∀ i, IsOpen (U i) ∧ Convex ℝ (U i) ∧ Bornology.IsBounded (U i)) ∧
      ∀ σ : Finset (Fin n), σ ∈ C ↔
        ∃ x : EuclideanSpace ℝ (Fin d), ∀ i, x ∈ U i ↔ i ∈ σ}

/-- **Conjecture 16** (arXiv v1, p. 14). Steiner triple codes have arbitrarily large open convex
embedding dimension. -/
theorem conjecture_16 (d : ℕ) (hd : 1 ≤ d) :
    ∃ n > 0, ∃ S : SteinerTripleSystem n,
      (d : ℕ∞) ≤ openEmbeddingDimension
        (S.blocks ∪ Finset.univ.image (fun i : Fin n ↦ {i}) ∪ {∅}) := by
  sorry

end Jeffs2026Embedding
