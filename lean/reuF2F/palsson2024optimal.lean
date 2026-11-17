import Mathlib

/-!
# On Optimal Point Sets Determining Distinct Triangles

Authors: Eyvindur A. Palsson and Edward Yu.
Origin: [Polymath Jr. 2023](https://geometrynyc.wixsite.com/polymathreu).
Reference: E. A. Palsson and E. Yu, *On Optimal Point Sets Determining Distinct Triangles*,
arXiv:2308.13107.
-/

noncomputable section

namespace Palsson2024Optimal

open Finset
open scoped Real

/-- The Euclidean plane, with the Euclidean norm. -/
abbrev Point2 := EuclideanSpace ℝ (Fin 2)

/-- The distinct-triangle count: unordered side-length multisets of triples of distinct points,
including collinear triples (Introduction). Squared distances are used, which identifies the
same congruence classes. -/
def distinctTriangleCount (P : Finset Point2) : ℕ :=
  #({abc ∈ (P.product P).product P |
      abc.1.1 ≠ abc.1.2 ∧ abc.1.1 ≠ abc.2 ∧ abc.1.2 ≠ abc.2}.image fun abc ↦
    ([(dist abc.1.1 abc.1.2 ^ 2), (dist abc.1.1 abc.2 ^ 2),
      (dist abc.1.2 abc.2 ^ 2)] : Multiset ℝ))

/-- The regular polygon, realized on the Euclidean unit circle. -/
def regularPolygon (n : ℕ) : Finset Point2 :=
  Finset.univ.image fun j : Fin n ↦
    WithLp.toLp 2 ![Real.cos (2 * π * (j : ℝ) / (n : ℝ)),
      Real.sin (2 * π * (j : ℝ) / (n : ℝ))]

/-- **Conjecture 4.1** (Section 4). The maximum number of points in the plane spanning four
distinct triangles is seven, achieved only by the regular heptagon. -/
theorem conjecture_4_1 :
    (#(regularPolygon 7) = 7 ∧ distinctTriangleCount (regularPolygon 7) = 4) ∧
      ∀ P : Finset Point2, distinctTriangleCount P = 4 →
        #P ≤ 7 ∧ (#P = 7 →
          (∃ scale > (0 : ℝ), ∃ e : Point2 ≃ᵢ Point2,
            (regularPolygon 7).image (fun p ↦ e (scale • p)) = P)) := by
  sorry

end Palsson2024Optimal
