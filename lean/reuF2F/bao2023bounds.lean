import Mathlib

/-!
# Bounds in simple hexagonal lattice and classification of 11-stick knots

Authors: Yueheng Bao, Ari Benveniste, Marion Campisi, Nicholas Cazet, Ansel Goh, Jiantong Liu,
and Ethan Sherman.
Origin: [Polymath Jr. 2022](https://geometrynyc.wixsite.com/polymathreu/results2022).
Reference: Y. Bao, A. Benveniste, M. Campisi, N. Cazet, A. Goh, J. Liu, and E. Sherman, *Bounds
in simple hexagonal lattice and classification of 11-stick knots*, J. Knot Theory Ramifications
**32** (2023), no. 14, 2350097; arXiv:2211.00687v2.
-/

namespace Bao2023Bounds

/-- A non-self-intersecting polygon: distinct vertices and straight edges meeting only at common
endpoints (Section 2). -/
structure PolygonalKnot (n : ℕ) extends Polygon (EuclideanSpace ℝ (Fin 3)) n where
  three_le : 3 ≤ n
  vertices_injective : Function.Injective toPolygon.vertices
  nondegenerate_edges : toPolygon.HasNondegenerateEdges
  simple : ∀ i j, i ≠ j →
    toPolygon.edgeSet ℝ i ∩ toPolygon.edgeSet ℝ j ⊆
      ({toPolygon i, toPolygon (finRotate n i)} ∩
        {toPolygon j, toPolygon (finRotate n j)})

/-- **Conjecture 2** (p. 20). Every knot admitting a simple-hexagonal lattice representative with
at most fourteen sticks has crossing number at most five.

The crossing number uses regular projections of arbitrary ambient-isotopic polygons, not only of
the given lattice representative. -/
theorem conjecture_2 {n : ℕ} (P : PolygonalKnot n) (hn : n ≤ 14)
    (hvertices : ∀ i, ∃ a b c : ℤ,
      P.toPolygon i = WithLp.toLp 2
        ![(a : ℝ) + (b : ℝ) / 2, (b : ℝ) * √3 / 2, (c : ℝ)])
    (hsticks : ∀ i, ∃ k ≠ (0 : ℤ),
      (P.toPolygon (finRotate n i) - P.toPolygon i =
          (k : ℝ) • WithLp.toLp 2 ![1, 0, 0] ∨
        P.toPolygon (finRotate n i) - P.toPolygon i =
          (k : ℝ) • WithLp.toLp 2 ![1 / 2, √3 / 2, 0] ∨
        P.toPolygon (finRotate n i) - P.toPolygon i =
          (k : ℝ) • WithLp.toLp 2 ![-1 / 2, √3 / 2, 0] ∨
        P.toPolygon (finRotate n i) - P.toPolygon i =
          (k : ℝ) • WithLp.toLp 2 ![0, 0, 1])) :
    ∃ m : ℕ, ∃ Q : PolygonalKnot m,
      ∃ H : unitInterval → (EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3)),
      Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ H p.1 p.2) ∧
      Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ (H p.1).symm p.2) ∧
      H 0 = Homeomorph.refl (EuclideanSpace ℝ (Fin 3)) ∧
      H 1 '' P.toPolygon.boundary ℝ = Q.toPolygon.boundary ℝ ∧
      let π : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2) :=
        fun p ↦ WithLp.toLp 2 ![p 0, p 1]
      (∀ i, π (Q.toPolygon i) ≠ π (Q.toPolygon (finRotate m i))) ∧
      (∀ i j, i ≠ j → i ≠ finRotate m j →
        π (Q.toPolygon i) ∉
          segment ℝ (π (Q.toPolygon j)) (π (Q.toPolygon (finRotate m j)))) ∧
      (∀ i j, i ≠ j →
        openSegment ℝ (π (Q.toPolygon i)) (π (Q.toPolygon (finRotate m i))) ∩
          openSegment ℝ (π (Q.toPolygon j)) (π (Q.toPolygon (finRotate m j))) ≠ ∅ →
        LinearIndependent ℝ
          ![π (Q.toPolygon (finRotate m i)) - π (Q.toPolygon i),
            π (Q.toPolygon (finRotate m j)) - π (Q.toPolygon j)]) ∧
      (∀ q, {p | p ∈ Q.toPolygon.boundary ℝ ∧ π p = q}.encard ≤ 2) ∧
      {q | ∃ p ∈ Q.toPolygon.boundary ℝ, ∃ r ∈ Q.toPolygon.boundary ℝ,
        p ≠ r ∧ π p = q ∧ π r = q}.encard ≤ 5 := by
  sorry

end Bao2023Bounds
