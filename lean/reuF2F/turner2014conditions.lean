import Mathlib

/-!
# Conditions for discrete equidecomposability of polygons

Authors: Paxton Turner and Yuhuai (Tony) Wu.
Origin: [Summer@ICERM 2014](https://icerm.brown.edu/summerug/2014/).
Reference: P. Turner and Y. Wu, *Conditions for discrete equidecomposability of polygons*,
arXiv:1412.0191v1, 2014.
-/

noncomputable section

namespace Turner2014Conditions

open Finset

/-- Finite rational boundary coordinates, each stored as an integer numerator and a natural
denominator minus one. -/
abbrev PolygonCode := List ((ℤ × ℕ) × (ℤ × ℕ))

/-- The cyclically ordered boundary vertices of a finite input code. -/
def polygon (c : PolygonCode) : Polygon (Fin 2 → ℝ) c.length where
  vertices i := ![((c.get i).1.1 : ℝ) / ((c.get i).1.2 + 1),
    ((c.get i).2.1 : ℝ) / ((c.get i).2.2 + 1)]

/-- The closed polygonal region bounded by a valid code: the boundary and the bounded components
of its complement. -/
def polygonRegion (c : PolygonCode) : Set (Fin 2 → ℝ) :=
  (polygon c).boundary ℝ ∪
    {x | x ∉ (polygon c).boundary ℝ ∧
      Bornology.IsBounded (connectedComponentIn ((polygon c).boundary ℝ)ᶜ x)}

/-- A finite rational triangulation, as a Mathlib simplicial complex (Section 3.1). -/
structure RationalTriangulation (P : Set (Fin 2 → ℝ)) extends
    Geometry.SimplicialComplex ℝ (Fin 2 → ℝ) where
  finite_faces : faces.Finite
  rational_vertices : ∀ x ∈ toSimplicialComplex.vertices, ∀ i,
    ∃ q : ℚ, (q : ℝ) = x i
  triangular_facets : ∀ s ∈ toSimplicialComplex.facets, #s = 3
  covers : toSimplicialComplex.space = P

/-- A facet map: a bijection of open triangular facets, with one integral affine-unimodular map
on each facet (Definition 3.1). Edges and vertices are ignored. -/
structure FacetMap {P Q : Set (Fin 2 → ℝ)}
    (T : RationalTriangulation P) (U : RationalTriangulation Q) where
  /-- The bijection between the facets of the two triangulations. -/
  matching : T.toSimplicialComplex.facets ≃ U.toSimplicialComplex.facets
  /-- The unimodular linear part of the affine map on each facet. -/
  linear : T.toSimplicialComplex.facets → Matrix.GeneralLinearGroup (Fin 2) ℤ
  /-- The integral translation part of the affine map on each facet. -/
  translation : T.toSimplicialComplex.facets → Fin 2 → ℤ
  maps_facets : ∀ s : T.toSimplicialComplex.facets,
    (fun x : Fin 2 → ℝ ↦
      Matrix.mulVec ((linear s).val.map (Int.castRingHom ℝ)) x +
        fun i ↦ (translation s i : ℝ)) ''
      interior (convexHull ℝ (s.val : Set (Fin 2 → ℝ))) =
        interior (convexHull ℝ ((matching s).val : Set (Fin 2 → ℝ)))

/-- **Conjecture 1.3** (first assertion). One total computable procedure decides rational
facet-map existence.

This uses Definition 3.1 and the existential refinement criterion of Proposition 3.15 and
Theorem 3.17, not the inconsistent all-multiples summary or the stronger single-base proposal
of Section 5(1). -/
theorem conjecture_1_3_facet_decidability :
    ∃ f : PolygonCode × PolygonCode → Bool, Computable f ∧
      ∀ (p q : PolygonCode)
        (hp : 3 ≤ p.length ∧ Function.Injective (polygon p).vertices ∧
          ∀ i j : Fin p.length, i ≠ j →
            (polygon p).edgeSet ℝ i ∩ (polygon p).edgeSet ℝ j =
              convexHull ℝ
                (({polygon p i, polygon p (finRotate p.length i)} : Set (Fin 2 → ℝ)) ∩
                  {polygon p j, polygon p (finRotate p.length j)}))
        (hq : 3 ≤ q.length ∧ Function.Injective (polygon q).vertices ∧
          ∀ i j : Fin q.length, i ≠ j →
            (polygon q).edgeSet ℝ i ∩ (polygon q).edgeSet ℝ j =
              convexHull ℝ
                (({polygon q i, polygon q (finRotate q.length i)} : Set (Fin 2 → ℝ)) ∩
                  {polygon q j, polygon q (finRotate q.length j)})),
        f (p, q) = true ↔
          ∃ (T : RationalTriangulation (polygonRegion p))
            (U : RationalTriangulation (polygonRegion q)), Nonempty (FacetMap T U) := by
  sorry

end Turner2014Conditions
