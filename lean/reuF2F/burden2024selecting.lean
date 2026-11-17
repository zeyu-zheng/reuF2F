import Mathlib

/-!
# Selecting balls from urns with partial replacement rules

Authors: Julian Burden, Chandramauli Chakraborty, Qizhou Fang, Lisa Lin,
Nasser Malibari, Sammi Matoush, Isaiah Milbank, Zahan Parekh, Martin Prado,
Rachael Ren, Qizhao Rong, Maximiliano Sanchez Garza, Eli Sun, Enrique Trevino,
and Daisuke Yamada.
Origin: [Polymath Jr. 2021](https://geometrynyc.wixsite.com/polymathreu/results2021).
Reference: J. Burden, C. Chakraborty, Q. Fang, L. Lin, N. Malibari, S. Matoush, I. Milbank,
Z. Parekh, M. Prado, R. Ren, Q. Rong, M. Sanchez Garza, E. Sun, E. Trevino, and D. Yamada,
*Selecting balls from urns with partial replacement rules*, PUMP J. Undergrad. Res. **7** (2024),
285-298.
-/

noncomputable section

namespace Burden2024Selecting

open scoped Topology

/-- The expected number `E(n, R, W)` of white draws, where white balls are removed and red balls
returned, via the zero-draw initial value and recurrence (1) (Section 1). -/
def expectedWhite : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 0
  | n + 1, R, W =>
      (W : ℝ) / ((R : ℝ) + W) * (1 + expectedWhite n R (W - 1)) +
        (R : ℝ) / ((R : ℝ) + W) * expectedWhite n R W

/-- **Conjecture 4.1** (p. 293). The diagonal expectation ratio is nonincreasing and converges to
the proposed sharp constant.

`W(1)` is specified as the positive root of `ω * exp ω = 1`. A November 2025 online argument
addresses only the limit, not the monotonicity. -/
theorem conjecture_4_1 :
    AntitoneOn (fun n : ℕ ↦ expectedWhite n n n / ((n : ℝ) / 2)) (Set.Ici 1) ∧
      ∃ ω > (0 : ℝ), ω * Real.exp ω = 1 ∧
        Filter.Tendsto (fun n : ℕ ↦ expectedWhite n n n / ((n : ℝ) / 2)) Filter.atTop
          (𝓝 (2 - 2 * Real.exp (-ω))) := by
  sorry

end Burden2024Selecting
