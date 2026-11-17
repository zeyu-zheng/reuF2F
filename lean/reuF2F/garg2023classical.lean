import Mathlib

/-!
# Classical and Consecutive Pattern Avoidance in Rooted Forests

Authors: Swapnil Garg and Alan Peng.
Origin: [University of Minnesota Duluth REU 2019](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: S. Garg and A. Peng, *Classical and consecutive pattern avoidance in rooted
forests*, J. Combin. Theory Ser. A **194** (2023), 105699; arXiv:2005.08889.
-/

namespace Garg2023Classical

/-- A classical pattern occurs in a word when a subsequence has exactly the same relative order
as the pattern (Section 2). -/
def Contains {k n : ℕ} (σ : Equiv.Perm (Fin k)) (w : List (Fin n)) : Prop :=
  ∃ i : Fin k → Fin w.length, StrictMono i ∧
    ∀ a b, w[i a] < w[i b] ↔ σ a < σ b

/-- The set `F_n(S)` of avoiding forests on `[n]` (Section 2). Forests are encoded by joining
their roots to an extra vertex `none`, which is omitted from label paths. -/
def avoidingForests (S : Finset ((k : ℕ) × Equiv.Perm (Fin (k + 1)))) (n : ℕ) :
    Set (SimpleGraph (Option (Fin n))) :=
  {G | G.IsTree ∧ ∀ v : Fin n, ∀ p : G.Path none (some v),
    ∀ σ ∈ S, ¬Contains σ.2 (p.val.support.filterMap id)}

/-- **Conjecture 7.3** (arXiv v2, p. 38). Forest-Wilf equivalence of two sets of patterns implies
their Wilf equivalence for permutations. -/
theorem conjecture_7_3
    (S T : Finset ((k : ℕ) × Equiv.Perm (Fin (k + 1))))
    (h : ∀ n, (avoidingForests S n).ncard = (avoidingForests T n).ncard)
    (n : ℕ) :
    {pi : Equiv.Perm (Fin n) | ∀ σ ∈ S,
      ¬Contains σ.2 (List.ofFn pi)}.ncard =
    {pi : Equiv.Perm (Fin n) | ∀ σ ∈ T,
      ¬Contains σ.2 (List.ofFn pi)}.ncard := by
  sorry

end Garg2023Classical
