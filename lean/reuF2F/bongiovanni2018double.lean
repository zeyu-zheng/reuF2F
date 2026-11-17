import Mathlib

/-!
# Double Bubbles on the Real Line with Log-Convex Density

Authors: Eliot Bongiovanni, Leonardo Di Giosia, Alejandro Diaz, Jahangir Habib,
Arjun Kakkar, Lea Kenigsberg, Dylanger Pittman, Nat Sothanaphan, and Weitao Zhu.
Origin: [Williams College SMALL REU 2016-2017](https://math.williams.edu/small/).
Reference: E. Bongiovanni, L. Di Giosia, A. Diaz, J. Habib, A. Kakkar, L. Kenigsberg, D. Pittman,
N. Sothanaphan, and W. Zhu, *Double bubbles on the real line with log-convex density*,
arXiv:1708.03289.
-/

noncomputable section

namespace Bongiovanni2018Double

open scoped Real Topology ENNReal
open Set Filter MeasureTheory

/-- The smoothed-out exponential density: `exp (x ^ 2)` inside `(-a, a)` and the tangent
continuation `exp (a * (2 * |x| - a))` outside (equation (6)). -/
def smoothedExpDensity (a x : ℝ) : ℝ :=
  if |x| < a then Real.exp (x ^ 2) else Real.exp (a * (2 * |x| - a))

/-- A finite one-dimensional double bubble: finitely many nondegenerate closed intervals, each
assigned to one of two regions. Intervals are ordered with disjoint interiors, and a shared
endpoint counts once in the perimeter. -/
structure FiniteDoubleBubble where
  /-- The number of interval components. -/
  m : ℕ
  /-- The left endpoint of each interval component. -/
  left : Fin m → ℝ
  /-- The right endpoint of each interval component. -/
  right : Fin m → ℝ
  /-- The enclosed region to which each interval component belongs. -/
  chamber : Fin m → Fin 2
  proper : ∀ i : Fin m, left i < right i
  ordered : ∀ i j : Fin m, i < j → right i ≤ left j
  different_chambers_at_shared_endpoint :
    ∀ i j : Fin m, i < j → right i = left j → chamber i ≠ chamber j

/-- The union of the components belonging to one region of a double bubble. -/
def regionSet (C : FiniteDoubleBubble) (k : Fin 2) : Set ℝ :=
  ⋃ i : Fin C.m, ⋃ _ : C.chamber i = k, Icc (C.left i) (C.right i)

/-- The weighted perimeter for density `g`: the sum of `g` over the distinct boundary points. -/
def weightedPerimeter (g : ℝ → ℝ) (C : FiniteDoubleBubble) : ℝ :=
  ∑ x ∈ (Finset.univ.image C.left) ∪ (Finset.univ.image C.right), g x

/-- The weighted volume of one region of a double bubble. -/
def weightedVolume (g : ℝ → ℝ) (C : FiniteDoubleBubble) (k : Fin 2) : ℝ :=
  ∑ i : Fin C.m, if C.chamber i = k then (∫ x in C.left i..C.right i, g x) else 0

/-- Perimeter minimization among finite interval competitors (Definition 2.1). Restricting to such
competitors is justified by the reduction at the start of Section 3. -/
def IsWeightedPerimeterMinimizing (g : ℝ → ℝ) (V₁ V₂ : ℝ) (C : FiniteDoubleBubble) : Prop :=
  (∀ x : ℝ, 0 < g x) ∧ (0 < V₁ ∧ 0 < V₂) ∧
    weightedVolume g C 0 = V₁ ∧ weightedVolume g C 1 = V₂ ∧
    ∀ D : FiniteDoubleBubble,
      weightedVolume g D 0 = V₁ → weightedVolume g D 1 = V₂ →
        weightedPerimeter g C ≤ weightedPerimeter g D

/-- The double-interval candidate, up to reflection of the two regions, with ordered boundary
points. -/
def IsDoubleIntervalCandidateUpToReflection (C : FiniteDoubleBubble) (x₁ x₂ x₃ : ℝ) : Prop :=
  (∀ i : Fin C.m, ∀ h : i.val + 1 < C.m,
    C.right i = C.left ⟨i.val + 1, h⟩) ∧
    C.m = 2 ∧ x₁ < x₂ ∧ x₂ < x₃ ∧
    ((Finset.univ.image C.left) ∪ (Finset.univ.image C.right)) = ({x₁, x₂, x₃} : Finset ℝ) ∧
    ((regionSet C 0 = Icc x₁ x₂ ∧ regionSet C 1 = Icc x₂ x₃) ∨
      (regionSet C 1 = Icc x₁ x₂ ∧ regionSet C 0 = Icc x₂ x₃))

/-- The triple-interval candidate: region `0` is the middle interval and region `1` is split
into the two flanking intervals; the target's `V₁ ≤ V₂` makes region `0` the smaller one. No
symmetry is imposed, matching the non-strict examples of Section 5. -/
def IsTripleIntervalCandidate (C : FiniteDoubleBubble) (x₁ x₂ x₃ x₄ : ℝ) : Prop :=
  (∀ i : Fin C.m, ∀ h : i.val + 1 < C.m,
    C.right i = C.left ⟨i.val + 1, h⟩) ∧
    C.m = 3 ∧ x₁ < x₂ ∧ x₂ < x₃ ∧ x₃ < x₄ ∧
    ((Finset.univ.image C.left) ∪ (Finset.univ.image C.right)) =
      ({x₁, x₂, x₃, x₄} : Finset ℝ) ∧
    regionSet C 0 = Icc x₂ x₃ ∧ regionSet C 1 = Icc x₁ x₂ ∪ Icc x₃ x₄

/-- **Conjecture 5.10**. The smoothed exponential density has a finite positive threshold
separating the all-double-interval regime from an increasing `C¹` double/triple tie curve with
the stated endpoint limits.

The density is only non-strictly log-convex, so Sothanaphan's theorem for strictly log-convex
densities does not apply to its affine logarithmic tails. -/
theorem conjecture_5_10_smoothed_exponential_threshold
    {a : ℝ} (ha : 2 * √(Real.log 2) < a) :
    let smoothed : ℝ → ℝ := smoothedExpDensity a
    let tie : ℝ → ℝ → Prop := fun V₁ V₂ ↦
      ∃ CD CT : FiniteDoubleBubble, ∃ x₁ x₂ x₃ y₁ y₂ y₃ y₄ : ℝ,
        let logDensity : ℝ → ℝ := fun x : ℝ ↦ Real.log (smoothed x)
        (∀ x : ℝ, 0 < smoothed x) ∧ (0 < V₁ ∧ 0 < V₂) ∧
          weightedVolume smoothed CD 0 = V₁ ∧ weightedVolume smoothed CD 1 = V₂ ∧
          weightedVolume smoothed CT 0 = V₁ ∧ weightedVolume smoothed CT 1 = V₂ ∧
          IsWeightedPerimeterMinimizing smoothed V₁ V₂ CD ∧
          IsWeightedPerimeterMinimizing smoothed V₁ V₂ CT ∧
          IsDoubleIntervalCandidateUpToReflection CD x₁ x₂ x₃ ∧
          (0 ≤ derivWithin logDensity (Ici x₁) x₁ + derivWithin logDensity (Ici x₂) x₂ +
              derivWithin logDensity (Ici x₃) x₃ ∧
            derivWithin logDensity (Iic x₁) x₁ + derivWithin logDensity (Iic x₂) x₂ +
              derivWithin logDensity (Iic x₃) x₃ ≤ 0) ∧
          IsTripleIntervalCandidate CT y₁ y₂ y₃ y₄ ∧
          ((0 ≤ derivWithin logDensity (Ici y₁) y₁ + derivWithin logDensity (Ici y₄) y₄ ∧
              derivWithin logDensity (Iic y₁) y₁ + derivWithin logDensity (Iic y₄) y₄ ≤ 0) ∧
            (0 ≤ derivWithin logDensity (Ici y₂) y₂ + derivWithin logDensity (Ici y₃) y₃ ∧
              derivWithin logDensity (Iic y₂) y₂ + derivWithin logDensity (Iic y₃) y₃ ≤ 0)) ∧
          weightedPerimeter smoothed CD = weightedPerimeter smoothed CT
    ∃ V₀ : ℝ, ∃ w : ℝ → ℝ,
      0 < V₀ ∧
        (∀ V₁ ≥ V₀, ∀ V₂ ≥ V₁,
          (∃ C : FiniteDoubleBubble, IsWeightedPerimeterMinimizing smoothed V₁ V₂ C) ∧
            ∀ C : FiniteDoubleBubble, IsWeightedPerimeterMinimizing smoothed V₁ V₂ C →
              ∃ x₁ x₂ x₃ : ℝ, IsDoubleIntervalCandidateUpToReflection C x₁ x₂ x₃) ∧
        (∀ V₁ > (0 : ℝ), V₁ < V₀ →
          V₁ ≤ w V₁ ∧
            (tie V₁ (w V₁) ∧
              ∀ W₂ ≥ V₁, tie V₁ W₂ → W₂ = w V₁) ∧
            (∀ V₂ ≥ V₁, V₂ < w V₁ →
              (∃ C : FiniteDoubleBubble, IsWeightedPerimeterMinimizing smoothed V₁ V₂ C) ∧
                ∀ C : FiniteDoubleBubble, IsWeightedPerimeterMinimizing smoothed V₁ V₂ C →
                  ∃ x₁ x₂ x₃ : ℝ, IsDoubleIntervalCandidateUpToReflection C x₁ x₂ x₃) ∧
            (∀ V₂ : ℝ, w V₁ < V₂ →
              (∃ C : FiniteDoubleBubble, IsWeightedPerimeterMinimizing smoothed V₁ V₂ C) ∧
                ∀ C : FiniteDoubleBubble, IsWeightedPerimeterMinimizing smoothed V₁ V₂ C →
                  ∃ x₁ x₂ x₃ x₄ : ℝ, IsTripleIntervalCandidate C x₁ x₂ x₃ x₄)) ∧
        StrictMonoOn w (Ioo 0 V₀) ∧ ContDiffOn ℝ 1 w (Ioo 0 V₀) ∧
        (∃ L > (0 : ℝ), Tendsto w (𝓝[>] 0) (𝓝 L)) ∧
        Tendsto w (𝓝[<] V₀) atTop := by
  sorry

end Bongiovanni2018Double
