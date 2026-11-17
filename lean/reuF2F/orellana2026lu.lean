import Mathlib

/-!
# LU Factorization of Discrete Random Matrices

Authors: Samuel Orellana Mateo, John Urschel, and Nicholas West.
Origin: [MIT MSRP 2025](https://oge.mit.edu/msrp/profiles/samuel-orellana-mateo/).
Reference: S. Orellana Mateo, J. Urschel, and N. West, *LU Factorization of Discrete Random
Matrices*, arXiv:2608.08998 (2026).
-/

noncomputable section

namespace Orellana2026LU

open scoped Topology

/-- **Open Problem 1.5**. The limiting probability that a fair binary matrix is strongly
nonsingular is strictly greater than 0.5 percent.

Every leading principal real determinant is tested, including the full matrix, in the original
order without pivoting or conditioning; the source directs the positive proof of this bound. -/
theorem open_problem_1_5 :
    ∃ L : ℝ, (1 : ℝ) / 200 < L ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          (Nat.card
            { A : Matrix (Fin (n + 1)) (Fin (n + 1)) Bool //
              ∀ k : Fin (n + 1),
                ((A.map (fun b : Bool ↦ if b then (1 : ℝ) else 0)).submatrix
                  (Fin.castLE (Nat.succ_le_of_lt k.isLt))
                  (Fin.castLE (Nat.succ_le_of_lt k.isLt))).det ≠ 0 } : ℝ) /
            (2 : ℝ) ^ ((n + 1) ^ 2))
        Filter.atTop (𝓝 L) := by
  sorry

end Orellana2026LU
