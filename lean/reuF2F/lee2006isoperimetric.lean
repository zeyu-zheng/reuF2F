import Mathlib

/-!
# Isoperimetric regions in surfaces and in surfaces with density

Author: Michelle Lee.
Origin: [Williams College SMALL REU](https://web.williams.edu/Mathematics/published.html).
Reference: M. Lee, *Isoperimetric regions in surfaces and in surfaces with density*, Rose-Hulman
Undergrad. Math. J. **7** (2006), no. 2, Article 15, 24 pp.;
https://scholar.rose-hulman.edu/rhumj/vol7/iss2/15/.
-/

noncomputable section

namespace Lee2006Isoperimetric

open Set MeasureTheory
open scoped ContDiff Real ENNReal

/-- The unit-radius circle times the Gaussian line (Section 7.1). It carries the intrinsic `L2`
product distance and circle period `2 * π`. -/
abbrev Cylinder := WithLp 2 (AddCircle (2 * π) × ℝ)

/-- Gaussian area on the quotient cylinder: circle arclength of total mass `2 * π` times the
normalized variance-one Gaussian measure. -/
def cylinderMeasure : Measure Cylinder :=
  letI : Fact (0 < 2 * π) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  ((volume : Measure (AddCircle (2 * π))).prod
    (ProbabilityTheory.gaussianReal 0 1)).map (WithLp.toLp 2)

/-- The weighted BV perimeter on the boundaryless cylinder. Test fields have compact support on
the quotient, not on a cut strip or lift, and are differentiated before angular evaluation. -/
def cylinderPerimeter (E : Set Cylinder) : ℝ≥0∞ :=
  letI : Fact (0 < 2 * π) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  let q : WithLp 2 (ℝ × ℝ) → Cylinder := fun z ↦
    WithLp.toLp 2 (((WithLp.ofLp z).1 : AddCircle (2 * π)), (WithLp.ofLp z).2)
  let σ : Cylinder → WithLp 2 (ℝ × ℝ) := fun z ↦
    WithLp.toLp 2 ((AddCircle.equivIoc (2 * π) 0 (WithLp.ofLp z).1 : ℝ),
      (WithLp.ofLp z).2)
  ⨆ (F : ContinuousMap Cylinder (WithLp 2 (ℝ × ℝ))),
    ⨆ (_ : ContDiff ℝ 1 (fun z ↦ F (q z))),
    ⨆ (_ : HasCompactSupport F),
    ⨆ (_ : ∀ z, ‖F z‖ ≤ 1),
      ENNReal.ofReal (∫ z in E,
        LinearMap.trace ℝ (WithLp 2 (ℝ × ℝ))
          (fderiv ℝ (fun w ↦ F (q w)) (σ z)).toLinearMap -
        (WithLp.ofLp z).2 * (WithLp.ofLp (F z)).2 ∂cylinderMeasure)

/-- **Conjecture 7.10** (p. 23). On the unit-radius Gaussian cylinder, essential non-meridional
constant-weighted-curvature boundaries minimize near zero and total mass, and vertical pairs
minimize throughout a neighborhood of half mass.

The radius is fixed to one. Milman covers the middle neighborhood at `T = π`, but his
end-regime theorem requires `T > π`. -/
theorem conjecture_7_10 :
    let q : WithLp 2 (ℝ × ℝ) → Cylinder := fun z ↦
      WithLp.toLp 2 (((WithLp.ofLp z).1 : AddCircle (2 * π)), (WithLp.ofLp z).2)
    ∃ etaZero etaTotal etaHalf : ℝ,
      0 < etaZero ∧ 0 < etaTotal ∧ 0 < etaHalf ∧
      ∀ (A : ℝ) (_ : 0 < A) (_ : A < 2 * π),
        ((A < etaZero ∨ 2 * π - A < etaTotal) →
          ∃ (γ : ℝ → WithLp 2 (ℝ × ℝ)) (k : ℤ),
            ContDiff ℝ ∞ γ ∧
            (∀ t, deriv γ t ≠ 0) ∧
            (∀ t, γ (t + 1) = γ t +
              WithLp.toLp 2 ((k : ℝ) * (2 * π), (0 : ℝ))) ∧
            k ≠ 0 ∧
            InjOn (fun t ↦ q (γ t)) (Ico 0 1) ∧
            (∃ s t, (WithLp.ofLp (γ s)).2 ≠ (WithLp.ofLp (γ t)).2) ∧
            (∃ K : ℝ, ∀ t,
              let v := deriv γ t
              ((WithLp.ofLp v).1 * (WithLp.ofLp (deriv (deriv γ) t)).2 -
                (WithLp.ofLp v).2 * (WithLp.ofLp (deriv (deriv γ) t)).1) / ‖v‖ ^ 3 +
                (WithLp.ofLp (γ t)).2 * (WithLp.ofLp v).1 / ‖v‖ = K) ∧
            ∃ c : Cylinder, c ∉ range (fun t ↦ q (γ t)) ∧
              let E := connectedComponentIn (range (fun t ↦ q (γ t)))ᶜ c
              NullMeasurableSet E cylinderMeasure ∧
              cylinderMeasure E = ENNReal.ofReal A ∧
              cylinderPerimeter E < ⊤ ∧
              ∀ (F : Set Cylinder) (_ : NullMeasurableSet F cylinderMeasure),
                cylinderMeasure F = ENNReal.ofReal A →
                  cylinderPerimeter E ≤ cylinderPerimeter F) ∧
        ((|A - π| < etaHalf) →
          ∃ θ : AddCircle (2 * π),
            let E : Set Cylinder := {z | ∃ t : ℝ,
              0 < t ∧ t < A ∧ (WithLp.ofLp z).1 = θ + (t : AddCircle (2 * π))}
            NullMeasurableSet E cylinderMeasure ∧
            cylinderMeasure E = ENNReal.ofReal A ∧
            cylinderPerimeter E < ⊤ ∧
            ∀ (F : Set Cylinder) (_ : NullMeasurableSet F cylinderMeasure),
              cylinderMeasure F = ENNReal.ofReal A →
                cylinderPerimeter E ≤ cylinderPerimeter F) := by
  sorry

end Lee2006Isoperimetric
