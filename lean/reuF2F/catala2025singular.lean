import Mathlib

/-!
# Singular Curves and Metric Lines in 2-Jet Space

Authors: Dani Catala and Miriam Vollmayr-Lee.
Origin: [University of Michigan REU
2025](https://lsa.umich.edu/content/dam/math-assets/reu-su22/2025/Catala%2C%20Dani-Singular%20Curves%20and%20Metric%20Lines%20in%202-Jet%20Space.pdf).
Reference: D. Catala and M. Vollmayr-Lee, *Singular curves and metric lines in 2-jet space*,
University of Michigan REU report (2025).
-/

open scoped Real Topology
open Set MeasureTheory

noncomputable section

namespace Catala2025Singular

/-- The domain `X̃`: positive parameters with a nondegenerate positive hill interval
(Section 3.3). -/
def periodDomain (b : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧ 0 < 2 * p.1 - b ^ 2 * p.2 ^ 2}

/-- The two-coordinate period map (Definition 11). The positive endpoint of the hill interval is
written as the positive root of `C - B * x - A * x ^ 2`. -/
def tildeTheta (a b : ℝ) (p : periodDomain b) : ℝ × ℝ :=
  let q : ℝ × ℝ := p.1
  let P := fun x : ℝ ↦ (1 - x ^ 2, b * x + a * x ^ 2)
  let G := fun x : ℝ ↦ (1 - q.1 * x ^ 2, q.2 * (b * x + a * x ^ 2))
  let A := q.1 ^ 2 + q.2 ^ 2 * a ^ 2
  let B := 2 * a * b * q.2 ^ 2
  let C := 2 * q.1 - b ^ 2 * q.2 ^ 2
  let x₁ := (-B + √(B ^ 2 + 4 * A * C)) / (2 * A)
  (∫ x in (0 : ℝ)..x₁,
      (1 - (P x).1) * (G x).1 /
        √(1 - ((G x).1 ^ 2 + (G x).2 ^ 2)),
   ∫ x in (0 : ℝ)..x₁,
      (P x).2 * (G x).2 /
        √(1 - ((G x).1 ^ 2 + (G x).2 ^ 2)))

/-- **Conjecture 13**. The image of the period map is open and simply connected. -/
theorem conjecture_13_open_and_simply_connected
    (a b : ℝ) (hparams : a ≠ 0 ∨ b ≠ 0) (hb : 0 < 2 - b ^ 2) :
    IsOpen (Set.range (tildeTheta a b)) ∧
      SimplyConnectedSpace (Set.range (tildeTheta a b)) := by
  sorry

end Catala2025Singular
