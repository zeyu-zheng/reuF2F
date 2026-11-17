import Mathlib

/-!
# Multi-crossing Number for Knots and the Kauffman Bracket Polynomial

Authors: Colin Adams, Orsola Capovilla-Searle, Jesse Freeman, Daniel Irvine,
Samantha Petti, Daniel Vitek, Ashley Weber, and Sicong Zhang.
Origin: [Williams College SMALL REU](https://math.williams.edu/small/research-publications/).
Reference: C. Adams, O. Capovilla-Searle, J. Freeman, D. Irvine, S. Petti, D. Vitek, A. Weber,
and S. Zhang, *Multi-crossing number for knots and the Kauffman bracket polynomial*, preprint
(2014); arXiv:1407.4485v1.
-/

noncomputable section

namespace Adams2018Multi

open Finset

/-- A finite simple spatial polygon representing a classical tame knot.
The number of edges is unrestricted, and collinear subdivisions are allowed. -/
structure PolygonalKnot (m : ℕ) extends Polygon (EuclideanSpace ℝ (Fin 3)) m where
  three_le : 3 ≤ m
  vertices_injective : Function.Injective toPolygon.vertices
  nondegenerate_edges : toPolygon.HasNondegenerateEdges
  simple : ∀ i j, i ≠ j →
    toPolygon.edgeSet ℝ i ∩ toPolygon.edgeSet ℝ j ⊆
      ({toPolygon i, toPolygon (finRotate m i)} ∩
        {toPolygon j, toPolygon (finRotate m j)})

/-- The planar projection of a spatial polygon onto its first two coordinates. Crossing heights
are read from the dropped third coordinate, not from separate labels. -/
def PolygonalKnot.projection {m : ℕ} (K : PolygonalKnot m) :
    Polygon (EuclideanSpace ℝ (Fin 2)) m where
  vertices i := WithLp.toLp 2 ![K.toPolygon i 0, K.toPolygon i 1]

/-- A projection with only transverse `n`-crossings, each in edge interiors. Crossing order comes
from the spatial lift, and subdivisions permit height changes between crossings. -/
structure MultiCrossingDiagram (n m : ℕ) extends PolygonalKnot m where
  projected_vertices_injective : Function.Injective toPolygonalKnot.projection.vertices
  projected_nondegenerate : toPolygonalKnot.projection.HasNondegenerateEdges
  projected_vertices_off_edges : ∀ i j, i ≠ j → i ≠ finRotate m j →
    toPolygonalKnot.projection i ∉ toPolygonalKnot.projection.edgeSet ℝ j
  transverse : ∀ i j, i ≠ j →
    openSegment ℝ (toPolygonalKnot.projection i)
        (toPolygonalKnot.projection (finRotate m i)) ∩
      openSegment ℝ (toPolygonalKnot.projection j)
        (toPolygonalKnot.projection (finRotate m j)) ≠ ∅ →
    LinearIndependent ℝ
      ![toPolygonalKnot.projection (finRotate m i) - toPolygonalKnot.projection i,
        toPolygonalKnot.projection (finRotate m j) - toPolygonalKnot.projection j]
  crossing_order : ∀ q : EuclideanSpace ℝ (Fin 2),
    let branches := {i : Fin m | q ∈ openSegment ℝ (toPolygonalKnot.projection i)
      (toPolygonalKnot.projection (finRotate m i))}
    2 ≤ branches.encard → branches.encard = (n : ℕ∞)

/-- The set of singular planar points of a diagram. -/
def MultiCrossingDiagram.crossingPoints {n m : ℕ} (D : MultiCrossingDiagram n m) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {q | ∃ i j : Fin m, i ≠ j ∧
    q ∈ openSegment ℝ (D.toPolygonalKnot.projection i)
      (D.toPolygonalKnot.projection (finRotate m i)) ∧
    q ∈ openSegment ℝ (D.toPolygonalKnot.projection j)
      (D.toPolygonalKnot.projection (finRotate m j))}

/-- The crossing-point set of a diagram is finite. -/
theorem MultiCrossingDiagram.finite_crossingPoints {n m : ℕ}
    (D : MultiCrossingDiagram n m) : D.crossingPoints.Finite := by
  let P := D.toPolygonalKnot.projection
  let A : Fin m → Set (EuclideanSpace ℝ (Fin 2)) := fun i ↦
    openSegment ℝ (P i) (P (finRotate m i))
  have hpair : ∀ i j : Fin m, i ≠ j → (A i ∩ A j).Finite := by
    intro i j hij
    by_cases he : A i ∩ A j = ∅
    · rw [he]
      exact Set.finite_empty
    · have hlin := D.transverse i j hij he
      apply Set.Subsingleton.finite
      intro x hx y hy
      rcases (hx.1 : x ∈ A i) with ⟨a, b, ha, hb, hab, hx₁⟩
      rcases (hx.2 : x ∈ A j) with ⟨c, d, hc, hd, hcd, hx₂⟩
      rcases (hy.1 : y ∈ A i) with ⟨e, f, he, hf, hef, hy₁⟩
      rcases (hy.2 : y ∈ A j) with ⟨g, h, hg, hh, hgh, hy₂⟩
      have ha' : a = 1 - b := by linarith
      have hc' : c = 1 - d := by linarith
      have he' : e = 1 - f := by linarith
      have hg' : g = 1 - h := by linarith
      have hrel : (b - f) • (P (finRotate m i) - P i) +
          (h - d) • (P (finRotate m j) - P j) = 0 := by
        rw [ha'] at hx₁
        rw [hc'] at hx₂
        rw [he'] at hy₁
        rw [hg'] at hy₂
        calc
          (b - f) • (P (finRotate m i) - P i) +
              (h - d) • (P (finRotate m j) - P j) =
            ((1 - b) • P i + b • P (finRotate m i)) -
              ((1 - f) • P i + f • P (finRotate m i)) -
              (((1 - d) • P j + d • P (finRotate m j)) -
                ((1 - h) • P j + h • P (finRotate m j))) := by module
          _ = 0 := by rw [hx₁, hy₁, hx₂, hy₂]; abel
      have hbf := (hlin.eq_zero_of_pair hrel).1
      have bf : b = f := sub_eq_zero.mp hbf
      have ae : a = e := by linarith
      rw [ae, bf] at hx₁
      exact hx₁.symm.trans hy₁
  have hu : (⋃ i : Fin m, ⋃ j : Fin m, ⋃ (_ : i ≠ j), A i ∩ A j).Finite :=
    Set.finite_iUnion fun i ↦ Set.finite_iUnion fun j ↦
      Set.finite_iUnion fun hij ↦ hpair i j hij
  apply hu.subset
  rintro q ⟨i, j, hij, hqi, hqj⟩
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j,
    Set.mem_iUnion.mpr ⟨hij, hqi, hqj⟩⟩⟩

/-- The `n`-crossing number: the least number of crossing points over all `n`-diagrams of the
same knot type. The value lies in `ℕ∞`, so it is `⊤` when no diagram exists. -/
def crossingNumber {k : ℕ} (K : PolygonalKnot k) (n : ℕ) : ℕ∞ :=
  sInf {c : ℕ∞ | ∃ m : ℕ, ∃ D : MultiCrossingDiagram n m,
    ∃ H : unitInterval → (EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3)),
      Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ H p.1 p.2) ∧
      Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ (H p.1).symm p.2) ∧
      H 0 = Homeomorph.refl (EuclideanSpace ℝ (Fin 3)) ∧
      H 1 '' K.toPolygon.boundary ℝ = D.toPolygonalKnot.toPolygon.boundary ℝ ∧
      c = (#D.finite_crossingPoints.toFinset : ℕ∞)}

/-- **Unnumbered conjecture** (Section 5, pp. 22-23). For every tame knot, including the unknot,
the `n`-crossing number does not increase when `n` increases by one. -/
theorem crossing_spectrum_monotone {k : ℕ} (K : PolygonalKnot k)
    (n : ℕ) (hn : 2 ≤ n) : crossingNumber K (n + 1) ≤ crossingNumber K n := by
  sorry

end Adams2018Multi
