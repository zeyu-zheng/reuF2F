import Mathlib

/-!
# Isoperimetric Pentagonal Tilings

Authors: Ping Ngai Chung, Miguel A. Fernandez, Yifei Li, Michael Mara, Frank Morgan,
Isamar Rosa Plata, Niralee Shah, Luis Sordo Vieira, and Elena Wikner.
Origin: Williams College SMALL REU.
Reference: P. N. Chung, M. A. Fernandez, Y. Li, M. Mara, F. Morgan, I. Rosa Plata, N. Shah,
L. Sordo Vieira, and E. Wikner, *Isoperimetric pentagonal tilings*, arXiv:1111.6161.
-/

noncomputable section

namespace Chung2012Isoperimetric

open Set Filter MeasureTheory
open scoped ENNReal Real

/-- A polygonal region: a compact region bounded by a simple polygonal loop (Definition 2.1).
Regular closedness excludes lower-dimensional pieces. -/
structure PolygonalRegion where
  /-- The number of sides of the boundary polygon. -/
  sides : ℕ
  three_le : 3 ≤ sides
  /-- The simple polygonal loop bounding the region. -/
  polygon : Polygon ℂ sides
  /-- The compact region as a subset of the plane. -/
  carrier : Set ℂ
  compact : IsCompact carrier
  regularClosed : closure (interior carrier) = carrier
  frontier_eq : frontier carrier = polygon.boundary ℝ
  simpleBoundary : Nonempty (AddCircle (1 : ℝ) ≃ₜ ↥(polygon.boundary ℝ))

/-- **Unnumbered conjecture** (Introduction; remarks after Theorem 3.5). Cairo and Prismatic
pentagons minimize the perimeter ratio even when nonconvex tiles are allowed.

Interfaces are counted once, and no periodicity or edge-to-edge condition is imposed. -/
theorem nonconvex_perimeter_bound {ι : Type*} (T : ι → PolygonalRegion)
    (hsides : ∀ i, (T i).sides ≤ 5)
    (harea : ∀ i, volume (T i).carrier = 1)
    (hdisjoint : Pairwise fun i j ↦ Disjoint (interior (T i).carrier)
      (interior (T j).carrier))
    (hcover : (⋃ i, (T i).carrier) = univ) :
    ENNReal.ofReal (√(2 + √3)) ≤
      limsup (fun R : ℝ ↦
        (Measure.hausdorffMeasure 1)
          ((⋃ i, frontier (T i).carrier) ∩ Metric.ball (0 : ℂ) R) /
            ENNReal.ofReal (π * R ^ 2)) atTop := by
  sorry

end Chung2012Isoperimetric
