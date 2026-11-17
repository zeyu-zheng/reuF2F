import Mathlib

/-!
# Balls Isoperimetric in R^n with Volume and Perimeter Densities r^m and r^k

Authors: Leonardo Di Giosia, Jahangir Habib, Lea Kenigsberg, Dylanger Pittman, and Weitao Zhu.
Origin: [Williams College SMALL REU 2016](https://arxiv.org/pdf/1610.05830v2).
Reference: L. Di Giosia, J. Habib, L. Kenigsberg, D. Pittman, and W. Zhu, *Balls Isoperimetric
in R^n with Volume and Perimeter Densities r^m and r^k*, arXiv:1610.05830 (2016), revised 2019.
-/

noncomputable section

namespace Di2016Balls

open scoped ENNReal

/-- The volume with radial density `r ^ m` (Notation 2.1). -/
def radialVolumeMeasure (n : ℕ) (m : ℝ) :
    MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)) :=
  MeasureTheory.Measure.withDensity MeasureTheory.volume
    (fun x ↦ ENNReal.ofReal (‖x‖ ^ m))

/-- The perimeter with radial density `r ^ k`, as weighted distributional variation. For `n ≥ 2`
and `k > 0` it agrees with the source's weighted perimeter up to null modifications. -/
def radialPerimeter (n : ℕ) (k : ℝ)
    (E : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨆ (F : TestFunction
    (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    (EuclideanSpace ℝ (Fin n)) 1),
  ⨆ (_ : ∀ x, ‖F x‖ ≤ ‖x‖ ^ k),
    ENNReal.ofReal (∫ x in E,
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (fderiv ℝ F x).toLinearMap)

/-- **Unnumbered conjecture** (corrected abstract, p. 1). Centered balls uniquely minimize
weighted perimeter at every positive finite weighted volume throughout the inclusive stability
range.

The domain `n ≥ 2` follows the cited predecessor and the source's `n > 1` lemmas; no convexity
of the generating curve is assumed, and uniqueness is up to null sets. McGillivray (J. Geom.
Anal. 33 (2023), art. 344, Theorem 1.1) proves planar uniqueness in a restricted range. -/
theorem centered_balls_unique
    (n : ℕ) (hn : 2 ≤ n) (m k : ℝ) (hm : 0 < m) (hk : 0 < k)
    (hstable : m ≤ k - k / ((n : ℝ) + k - 1))
    (v : ℝ≥0∞) (hv : 0 < v) (hvfinite : v < ⊤) :
    ∃ r > (0 : ℝ),
      radialVolumeMeasure n m (Metric.ball 0 r) = v ∧
      ∀ E : Set (EuclideanSpace ℝ (Fin n)),
        MeasureTheory.NullMeasurableSet E MeasureTheory.volume →
        radialVolumeMeasure n m E = v →
        radialPerimeter n k (Metric.ball 0 r) ≤ radialPerimeter n k E ∧
          (radialPerimeter n k E = radialPerimeter n k (Metric.ball 0 r) →
            radialVolumeMeasure n m (symmDiff E (Metric.ball 0 r)) = 0) := by
  sorry

end Di2016Balls
