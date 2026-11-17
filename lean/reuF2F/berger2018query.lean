import Mathlib

/-!
# Query Complexity of Mastermind Variants

Authors: Aaron Berger, Christopher Chute, and Matthew Stone.
Origin: [Yale SUMRY 2015](https://sumry.yale.edu/past-projects).
Reference: A. Berger, C. Chute, and M. Stone, *Query Complexity of Mastermind Variants*,
arXiv:1607.04597v2 (2017).
-/

noncomputable section

namespace Berger2018Query

open Finset

/-- The black-peg count: the number of positions where query and hidden word agree (p. 3). -/
def blackPegs {n k : ℕ} (query hidden : Fin n → Fin k) : ℕ :=
  #{i | query i = hidden i}

/-- The white-peg count: the largest black-peg count over all permutations of the query
positions, minus the black-peg count (p. 3). -/
def whitePegs {n k : ℕ} (query hidden : Fin n → Fin k) : ℕ :=
  (univ.sup fun σ : Equiv.Perm (Fin n) ↦ blackPegs (fun i ↦ query (σ i)) hidden) -
    blackPegs query hidden

/-- **Problem 3** (Section 5, p. 15). Non-adaptive black-and-white Mastermind without repeated
colors needs `Ω(n log k)` queries, uniformly for all `k ≥ n`.

Identification uses the full ordered response vector with no final charged guess; colors do not
repeat within a query, but whole queries may repeat. -/
theorem problem_3 :
    ∃ c > (0 : ℝ), ∃ N ≥ 2, ∀ n ≥ N, ∀ k ≥ n, ∀ (m : ℕ) (queries : Fin m → Fin n ↪ Fin k),
      Function.Injective (fun hidden : Fin n ↪ Fin k ↦
        fun t ↦ (blackPegs (queries t) hidden, whitePegs (queries t) hidden)) →
      c * n * Real.logb 2 k ≤ m := by
  sorry

end Berger2018Query
