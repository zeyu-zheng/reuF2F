import Mathlib

/-!
# On the Speed of an Excited Asymmetric Random Walk

Authors: Mike Cinkoske, Joe Jackson, and Claire Plunkett.
Origin: [Purdue PRiME 2017](https://www.math.purdue.edu/research/past-research-projects.html).
Reference: M. Cinkoske, J. Jackson, and C. Plunkett, *On the Speed of an Excited Asymmetric
Random Walk*, Rose-Hulman Undergrad. Math. J. **19** (2018), no. 1, Article 6; arXiv:1708.08576v2.
-/

noncomputable section

namespace Cinkoske2017Speed

open MeasureTheory Filter
open scoped Topology

/-- The excited walk's visited sites in reverse chronological order, starting at zero, using
one independent uniform coordinate for each departure (Section 1). -/
def walkHistory (M : ℕ) (p : ℝ) (u : ℕ → unitInterval) : ℕ → List ℤ
  | 0 => [0]
  | n + 1 =>
      let h := walkHistory M p u n
      let x := h.headD 0
      let threshold : ℝ := if h.count x ≤ M then p else 1 / 2
      (x + if (u n : ℝ) < threshold then 1 else -1) :: h

/-- **Open question** (Section 4.3, p. 16). Spreading the same total drift over more equal
cookies makes the deterministic limiting speed nonincreasing.

The affirmative direction follows the decreasing-speed prediction on p. 16 and the question's
non-strict inequality; the added-cookie index includes zero. -/
theorem speed_nonincreasing (M : ℕ) (hM : 3 ≤ M) (p : ℝ)
    (hp : 0 < p) (hp_one : p < 1) (hdrift : 2 < (M : ℝ) * (2 * p - 1)) :
    ∃ v : ℕ → ℝ,
      (∀ i : ℕ,
        ∀ᵐ u ∂(Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure unitInterval))),
          Tendsto (fun n : ℕ ↦
            (((walkHistory (M + i)
              (1 / 2 + (M : ℝ) * (2 * p - 1) / (2 * ((M + i : ℕ) : ℝ)))
              u n).headD 0 : ℤ) : ℝ) / (n : ℝ)) atTop (𝓝 (v i))) ∧
      ∀ i : ℕ, v (i + 1) ≤ v i := by
  sorry

end Cinkoske2017Speed
