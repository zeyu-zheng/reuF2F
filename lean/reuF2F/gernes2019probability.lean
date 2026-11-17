import Mathlib

/-!
# The Probability of Easily Approximating the Positive Real Roots of Trinomials

Authors: Lauren Gernes and Laurel Newman.
Origin: [Texas A&M University REU
2019](https://artsci.tamu.edu/mathematics/academics/undergraduate/research/reu/results/results-2019.html).
Reference: L. Gernes and L. Newman, *The Probability of Easily Approximating the Positive Real
Roots of Trinomials*, REU report, October 25, 2019, 17 pp.
-/

noncomputable section

namespace Gernes2019Probability

/-- The failure set with normalized null vector `(a / b - 1, 1, -a / b)` (Definition 3.5). Its
three-term threshold follows the same authors' slide clarification, not the printed text. -/
def failureSet (a b : ℕ) : Set (Fin 3 → ℝ) :=
  let r := (a : ℝ) / (b : ℝ)
  {c | c 0 * c 1 < 0 ∧ c 2 * c 1 < 0 ∧
    0 < Real.log |c 1| - (1 - r) * Real.log |c 0| - r * Real.log |c 2| ∧
    Real.log |c 1| - (1 - r) * Real.log |c 0| - r * Real.log |c 2| ≤
      -(1 - r) * Real.log (1 - r) - r * Real.log r}

/-- **Conjecture 1**. The unconditional Gaussian failure probability satisfies the full uniform
three-regime envelope in exponent spread and middle scale.

Sigma denotes standard deviation, as in the experiment, with independent sampling. -/
theorem conjecture_1 :
    ∃ Csmall Cmiddle Clarge : ℝ,
      0 < Csmall ∧ 0 < Cmiddle ∧ 0 < Clarge ∧
      ∀ (a b : ℕ) (ha : 0 < a) (hab : a < b)
        (σ : ℝ) (hσ : 0 < σ),
        ((MeasureTheory.Measure.pi fun i : Fin 3 ↦
          ProbabilityTheory.gaussianReal 0
            (if i = 1 then Real.toNNReal (σ ^ 2) else 1))
          (failureSet a b)).toReal ≤
          min (Csmall * √(min (a : ℝ) ((b : ℝ) - (a : ℝ)) / (b : ℝ)) * σ)
            (min (Cmiddle * √(min (a : ℝ) ((b : ℝ) - (a : ℝ)) / (b : ℝ)))
              (Clarge * √(min (a : ℝ) ((b : ℝ) - (a : ℝ)) / (b : ℝ)) * σ ^ (-(37 : ℝ) / 50))) := by
  sorry

end Gernes2019Probability
