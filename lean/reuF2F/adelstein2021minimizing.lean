import Mathlib

/-!
# Minimizing Closed Geodesics on Polygons and Disks

Authors: Ian Adelstein, Arthur Azvolinsky, Joshua Hinman, and Alexander Schlesinger.
Origin: [Yale SUMRY](https://sumry.yale.edu/pastprojects).
Reference: I. Adelstein, A. Azvolinsky, J. Hinman, and A. Schlesinger, *Minimizing closed
geodesics on polygons and disks*, arXiv:1909.09274.
-/

noncomputable section

namespace Adelstein2021Minimizing

open scoped Real

/-- The filled regular polygon with circumradius one. -/
def regularPolygonSet (n : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  convexHull ℝ (Set.range fun i : Fin n ↦
    WithLp.toLp 2 ![Real.cos (2 * π * (i : ℝ) / (n : ℝ)),
      Real.sin (2 * π * (i : ℝ) / (n : ℝ))])

/-- The boundary-to-polygon inclusion, with both subtypes carrying the Euclidean metric. -/
def polygonSeamInclusion (n : ℕ)
    (x : frontier (regularPolygonSet n)) : regularPolygonSet n :=
  ⟨x.1, (frontier_subset_iff_isClosed.mpr
    ((Set.finite_range (fun i : Fin n ↦
      WithLp.toLp 2 ![Real.cos (2 * π * (i : ℝ) / (n : ℝ)),
        Real.sin (2 * π * (i : ℝ) / (n : ℝ))])).isClosed_convexHull ℝ)) x.2⟩

/-- The seam inclusion preserves Euclidean distances by the subtype metric. -/
lemma polygonSeamInclusion_isometry (n : ℕ) : Isometry (polygonSeamInclusion n) := by
  intro x y
  rfl

/-- The space `X_n`: two Euclidean copies of the filled polygon glued isometrically along their
common boundary. The nonemptiness of the seam is a hypothesis supplied in the target. -/
abbrev DoubledPolygon (n : ℕ) [Nonempty (frontier (regularPolygonSet n))] :=
  Metric.GlueSpace (polygonSeamInclusion_isometry n) (polygonSeamInclusion_isometry n)

/-- A closed geodesic: a positive-period, unit-speed, locally distance-minimizing map. -/
structure ClosedGeodesic (X : Type*) [MetricSpace X] where
  /-- The unit-speed periodic parametrisation. -/
  toFun : ℝ → X
  /-- The period, equal to the length of the geodesic. -/
  length : ℝ
  length_pos : 0 < length
  periodic : Function.Periodic toFun length
  locally_minimizing : ∀ t : ℝ, ∃ ε > (0 : ℝ),
    ∀ a b : ℝ, |a - t| < ε → |b - t| < ε →
      dist (toFun a) (toFun b) = |b - a|

/-- A `1 / k` geodesic: every subarc of length `L / k` minimizes distance (Section 1). -/
def ClosedGeodesic.IsOneOverK {X : Type*} [MetricSpace X]
    (γ : ClosedGeodesic X) (k : ℕ) : Prop :=
  2 ≤ k ∧ ∀ t : ℝ,
    dist (γ.toFun t) (γ.toFun (t + γ.length / (k : ℝ))) = γ.length / (k : ℝ)

/-- **Unnumbered conjecture** (tightness, after Corollary 1.2). The minimizing index of the
doubled odd regular `n`-gon is twice its smallest prime divisor.

Positive-length closed geodesics are the contextual convention; unit speed is a
reparametrization, not an extra geometric restriction. -/
theorem conjecture_odd_regular_polygon_corollary_1_2_bound_is_tight
    (n d : ℕ) (hn : 3 ≤ n) (hn_odd : Odd n)
    (hd_prime : Nat.Prime d) (hd_dvd : d ∣ n)
    (hd_min : ∀ q : ℕ, Nat.Prime q → q ∣ n → d ≤ q) :
    ∃ hseam : Nonempty (frontier (regularPolygonSet n)),
      letI := hseam
      (∃ γ : ClosedGeodesic (DoubledPolygon n), γ.IsOneOverK (2 * d)) ∧
        ∀ k : ℕ, (∃ γ : ClosedGeodesic (DoubledPolygon n), γ.IsOneOverK k) →
          2 * d ≤ k := by
  sorry

end Adelstein2021Minimizing
