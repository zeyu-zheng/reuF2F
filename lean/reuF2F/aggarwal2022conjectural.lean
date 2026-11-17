import Mathlib

/-!
# A conjectural asymptotic formula for multiplicative chaos in number theory

Authors: Daksh Aggarwal, Unique Subedi, William Verreault, Asif Zaman, and Chenghui Zheng.
Origin: [Fields Undergraduate Summer Research Program
2020](https://www.fields.utoronto.ca/activities/20-21/2020-FUSRP).
Reference: D. Aggarwal, U. Subedi, W. Verreault, A. Zaman, and C. Zheng, *A conjectural
asymptotic formula for multiplicative chaos in number theory*, preprint (2021), 18 pp.;
arXiv:2108.11367v1.
-/

noncomputable section

open scoped Topology
open MeasureTheory ProbabilityTheory Filter

namespace Aggarwal2022Conjectural

/-- The coefficient `A(n)` in (1.1), via the partition expansion (2.1)-(2.2). Coordinate
`i : Fin n` represents `X(i + 1)`. -/
def A (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ p : Nat.Partition n, ∏ i : Fin n,
    (x i / √(i.val + 1)) ^ p.parts.count (i.val + 1) /
      (Nat.factorial (p.parts.count (i.val + 1)) : ℝ)

/-- **Conjecture 1.4**. For both real standard Gaussian and uniform-sign inputs,
`(log N) ^ (1 / 4) E[|A(N)|]` tends to a finite positive law-dependent constant.

The finite product laws model the first `N` coordinates of each iid sequence, and the limit is
along all natural `N`; the complex-Gaussian case (Conjecture 1.1) is not included. -/
theorem conjecture_1_4 :
    ∃ C_R C_S : ℝ, 0 < C_R ∧ 0 < C_S ∧
      Tendsto (fun N : ℕ ↦
        Real.log (N : ℝ) ^ (1 / 4 : ℝ) *
          ∫ x : Fin N → ℝ, |A N x|
            ∂(Measure.pi (fun _ : Fin N ↦ gaussianReal 0 1)))
        atTop (𝓝 C_R) ∧
      Tendsto (fun N : ℕ ↦
        Real.log (N : ℝ) ^ (1 / 4 : ℝ) *
          ∫ x : Fin N → ℝ, |A N x|
            ∂(Measure.pi (fun _ : Fin N ↦
              bernoulliMeasure (1 : ℝ) (-1) ⟨(1 : ℝ) / 2, by norm_num⟩)))
        atTop (𝓝 C_S) := by sorry

end Aggarwal2022Conjectural
