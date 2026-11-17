import Mathlib

/-!
# Return Probabilities of Skip-Free Random Walks

Author: Andrew Lin.
Origin: [Caltech SURF 2021](https://web.stanford.edu/~lindrew/SURFreport.pdf).
Reference: A. Lin, *Return Probabilities of Skip-Free Random Walks*, SURF report, 2021.
-/

noncomputable section

namespace Lin2021Return

/-- **Problem 4**. For the infinite-line skip-free random walk with allowed jumps
`-1, 0, …, k - 1`, if `p_1, …, p_k ≤ 1 / (k + 1)`, then `p_{k+1}` is at most one of the first
`k` return probabilities. -/
theorem problem_4_infinite_line_skip_free_return_probability
    {k : ℕ} (hk : 0 < k) (a : Fin (k + 1) → ℝ)
    (ha_nonneg : ∀ j, 0 ≤ a j) (ha_sum : ∑ j, a j = 1) :
    let p : ℕ → ℝ := fun n ↦
      ∑ path : Fin n → Fin (k + 1),
        if (∑ t, ((path t : ℤ) - 1)) = 0 then ∏ t, a (path t) else 0
    (∀ i ∈ Finset.Icc 1 k, p i ≤ 1 / ((k : ℝ) + 1)) →
      ∃ m ∈ Finset.Icc 1 k, p (k + 1) ≤ p m := by sorry

end Lin2021Return
