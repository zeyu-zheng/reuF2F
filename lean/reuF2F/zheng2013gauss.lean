import Mathlib

/-!
# Gauss Sphere Problem with Polynomials

Author: Fan Zheng.
Origin: [MIT SPUR 2013](https://math.mit.edu/research/undergraduate/spur/past-projects.html).
Reference: F. Zheng, *Gauss Sphere Problem with Polynomials*, arXiv:1312.0108v1 (2013).
-/

noncomputable section

namespace Zheng2013Gauss

open MeasureTheory

/-- **Conjecture 1** (arXiv v1, p. 9). The sum of a homogeneous polynomial with zero spherical
mean over the integer points in a ball has error exponent at most its degree plus one, with any
positive loss.

The polynomial summand omitted on the MIT report's p. 9 is included, as in the arXiv version;
the bound is for all real radii and all such polynomials, not only harmonic ones. -/
theorem conjecture_1 (degree : ℕ) (P : MvPolynomial (Fin 3) ℂ)
    (homogeneous : P.IsHomogeneous degree)
    (mean_zero :
      (∫ x, P.eval (fun i ↦ (x.val i : ℂ))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) = 0) :
    let latticeBall := fun R : ℝ ↦
      ({z ∈ Fintype.piFinset (fun _ : Fin 3 ↦ Finset.Icc (-Int.ceil R) (Int.ceil R)) |
        ‖WithLp.toLp 2 (fun i ↦ (z i : ℝ))‖ ≤ R} : Finset (Fin 3 → ℤ))
    ∀ ε > (0 : ℝ),
      ∃ C > (0 : ℝ), ∃ R₀ ≥ (1 : ℝ),
        ∀ R ≥ R₀,
          ‖∑ z ∈ latticeBall R, P.eval (fun i ↦ (z i : ℂ))‖ ≤
              C * R ^ ((degree : ℝ) + 1 + ε) := by
  sorry

end Zheng2013Gauss
