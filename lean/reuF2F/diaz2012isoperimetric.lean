import Mathlib

/-!
# Isoperimetric problems in sectors with density

Authors: Alexander Diaz, Nate Harman, Sean Howe, and David Thompson.
Origin: [Williams College SMALL REU 2009](https://web.williams.edu/Mathematics/fmorgan/G09.pdf).
Reference: A. Diaz, N. Harman, S. Howe, and D. Thompson, *Isoperimetric problems in sectors with
density*, Adv. Geom. **12** (2012), 589--619.
-/

open Set MeasureTheory
open scoped Real ENNReal

noncomputable section

namespace Diaz2012Isoperimetric

/-- The weighted area for density `r ^ p`, in unwrapped polar coordinates (Section 2). -/
def sectorArea (p : ℝ) (E : Set (ℝ × ℝ)) : ℝ≥0∞ :=
  ∫⁻ x in E, ENNReal.ofReal (x.1 ^ (p + 1))

/-- The relative weighted perimeter in the sector, given by the distributional flux in polar
coordinates (Section 2). Boundary rays are not counted. -/
def sectorPerimeter (p θ : ℝ) (E : Set (ℝ × ℝ)) : ℝ≥0∞ :=
  ⨆ (F : (ℝ × ℝ) → (ℝ × ℝ)) (_ : ContDiff ℝ 1 F)
    (_ : HasCompactSupport F)
    (_ : tsupport F ⊆ {x | 0 < x.1 ∧ 0 < x.2 ∧ x.2 < θ})
    (_ : ∀ x, (F x).1 ^ 2 + (F x).2 ^ 2 ≤ 1),
    ENNReal.ofReal (∫ x in E,
      (fderiv ℝ (fun y : ℝ × ℝ ↦ y.1 ^ (p + 1) * (F y).1) x) (1, 0) +
      (fderiv ℝ (fun y : ℝ × ℝ ↦ y.1 ^ p * (F y).2) x) (0, 1))

/-- **Conjecture 4.18**. For every positive density exponent, the two transition angles in
Theorem 4.17 are `π / √(p + 1)` and `π * (p + 2) / (2 * p + 2)`.

The centered-circle part has a later resolution; both angles are retained. -/
theorem conjecture_4_18 (p : ℝ) (hp : 0 < p) :
    let U := fun θ : ℝ ↦
      {x : ℝ × ℝ | 0 < x.1 ∧ 0 < x.2 ∧ x.2 < θ}
    let D := fun R : ℝ ↦
      {x : ℝ × ℝ | 0 < x.1 ∧ 0 < x.2 ∧ x.2 < π / 2 ∧
        x.1 < 2 * R * Real.cos x.2}
    sSup {θ : ℝ | 0 < θ ∧
      ∀ R > (0 : ℝ), ∀ E : Set (ℝ × ℝ),
        MeasurableSet E → E ⊆ U θ →
          sectorArea p E = sectorArea p {x : ℝ × ℝ | x ∈ U θ ∧ x.1 < R} →
          sectorPerimeter p θ {x : ℝ × ℝ | x ∈ U θ ∧ x.1 < R} ≤ sectorPerimeter p θ E} =
        π / √(p + 1) ∧
    sInf {θ : ℝ | π / 2 ≤ θ ∧
      ∀ R > (0 : ℝ), ∀ E : Set (ℝ × ℝ),
        MeasurableSet E → E ⊆ U θ → sectorArea p E = sectorArea p (D R) →
          sectorPerimeter p θ (D R) ≤ sectorPerimeter p θ E} =
        π * (p + 2) / (2 * p + 2) := by
  sorry

end Diaz2012Isoperimetric
