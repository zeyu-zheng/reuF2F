import Mathlib

/-!
# Densities of Hyperbolic Cusp Invariants

Authors: Colin Adams, Rose Kaplan-Kelly, Michael Moore, Brandon Shapiro, Shruthi Sridhar, and
Joshua Wakefield.
Origin: [Williams College SMALL REU 2016](https://math.williams.edu/small/research-publications/).
Reference: C. Adams, R. Kaplan-Kelly, M. Moore, B. Shapiro, S. Sridhar, and J. Wakefield,
*Densities of hyperbolic cusp invariants of knots and links*, Proc. Amer. Math. Soc. **146**
(2018), no. 9, 4073-4089; arXiv:1701.03479v1.
-/

noncomputable section

namespace Adams2017Densities

open Set Topology MeasureTheory
open scoped ENNReal

/-- A tame link represented by finitely many disjoint embedded polygonal circles. -/
structure PolygonalLink where
  /-- The number of link components. -/
  components : ℕ
  components_pos : 0 < components
  /-- The number of vertices of each component polygon. -/
  size : Fin components → ℕ
  /-- The closed space polygon forming each component. -/
  polygon : (i : Fin components) → Polygon (EuclideanSpace ℝ (Fin 3)) (size i)
  size_ge_three : ∀ i, 3 ≤ size i
  vertices_injective : ∀ i, Function.Injective (polygon i).vertices
  edges_nondegenerate : ∀ i, (polygon i).HasNondegenerateEdges
  simple : ∀ i j k, j ≠ k →
    (polygon i).edgeSet ℝ j ∩ (polygon i).edgeSet ℝ k ⊆
      ({polygon i j, polygon i (finRotate (size i) j)} ∩
        {polygon i k, polygon i (finRotate (size i) k)})
  components_disjoint : ∀ i j, i ≠ j →
    Disjoint ((polygon i).boundary ℝ) ((polygon j).boundary ℝ)

/-- The geometric link, including every point on its component edges. -/
def PolygonalLink.carrier (L : PolygonalLink) : Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ i, (L.polygon i).boundary ℝ

/-- The link complement in `S³`, modeled by the one-point compactification of `ℝ³`. -/
abbrev PolygonalLink.complement (L : PolygonalLink) :=
  {x : OnePoint (EuclideanSpace ℝ (Fin 3)) | x ∉ OnePoint.some '' L.carrier}

/-- A link conformation whose horizontal projection is a regular link diagram. -/
structure LinkDiagram extends PolygonalLink where
  regular :
    let proj : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2) :=
      fun x ↦ WithLp.toLp 2 ![x 0, x 1]
    (∀ i j, proj (polygon i j) ≠ proj (polygon i (finRotate (size i) j))) ∧
    (∀ (i k : Fin components) (j : Fin (size i)) (l : Fin (size k)),
      proj (polygon i j) ∈ segment ℝ (proj (polygon k l))
        (proj (polygon k (finRotate (size k) l))) →
      polygon i j = polygon k l ∨ polygon i j = polygon k (finRotate (size k) l)) ∧
    (∀ (i k : Fin components) (j : Fin (size i)) (l : Fin (size k)),
      polygon i j ≠ polygon k l →
      (openSegment ℝ (proj (polygon i j))
        (proj (polygon i (finRotate (size i) j))) ∩
      openSegment ℝ (proj (polygon k l))
        (proj (polygon k (finRotate (size k) l)))).Nonempty →
      LinearIndependent ℝ
        ![proj (polygon i (finRotate (size i) j)) - proj (polygon i j),
          proj (polygon k (finRotate (size k) l)) - proj (polygon k l)]) ∧
    (∀ q, {x | x ∈ toPolygonalLink.carrier ∧ proj x = q}.encard ≤ 2)

/-- The minimal crossing number c(L), over all regular diagrams of its ambient isotopy type. -/
def PolygonalLink.crossingNumber (L : PolygonalLink) : ℕ :=
  sInf {n | ∃ D : LinkDiagram,
    ∃ H : unitInterval →
      (EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3)),
    Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ H p.1 p.2) ∧
    Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ (H p.1).symm p.2) ∧
    H 0 = Homeomorph.refl (EuclideanSpace ℝ (Fin 3)) ∧
    H 1 '' L.carrier = D.toPolygonalLink.carrier ∧
    let proj : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2) :=
      fun x ↦ WithLp.toLp 2 ![x 0, x 1]
    {q | ∃ x ∈ D.toPolygonalLink.carrier, ∃ y ∈ D.toPolygonalLink.carrier,
      x ≠ y ∧ proj x = q ∧ proj y = q}.encard = n}

/-- The upper-half-space model of hyperbolic three-space used to describe lifted cusps. -/
abbrev upperHalfSpace := {x : EuclideanSpace ℝ (Fin 3) | 0 < x 2}

/-- A complete finite-volume hyperbolic metric on the link complement in `S³`. -/
structure HyperbolicStructure (L : PolygonalLink) where
  /-- The hyperbolic metric on the link complement. -/
  metric : MetricSpace L.complement
  topology_eq : metric.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace L.complement)
  /-- The universal covering map from upper half-space to the complement. -/
  cover : C(upperHalfSpace, L.complement)
  covering : IsCoveringMap cover
  cover_surjective : Function.Surjective cover
  locally_hyperbolic : ∀ x : upperHalfSpace,
    ∃ U : Set upperHalfSpace, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U,
        @dist L.complement metric.toDist (cover y) (cover z) =
          2 * Real.arsinh (dist y.val z.val / (2 * √(y.val 2 * z.val 2)))
  complete : @CompleteSpace L.complement metric.toUniformSpace
  finite_volume :
    @Measure.euclideanHausdorffMeasure L.complement
      (@MetricSpace.toEMetricSpace L.complement metric)
      (@borel L.complement metric.toUniformSpace.toTopologicalSpace)
      (@BorelSpace.mk L.complement metric.toUniformSpace.toTopologicalSpace
        (@borel L.complement metric.toUniformSpace.toTopologicalSpace) rfl)
      3 (univ : Set L.complement) < ⊤

/-- An open torus cusp whose connected lifts are geometric horoballs. -/
structure Cusp {L : PolygonalLink} (H : HyperbolicStructure L) where
  /-- The open cusp region in the link complement. -/
  region : Set L.complement
  isOpen_region : IsOpen region
  torus_end : Nonempty (region ≃ₜ ((Fin 2 → AddCircle (1 : ℝ)) × Ioi (0 : ℝ)))
  horoball_lifts : ∀ x : upperHalfSpace, H.cover x ∈ region →
    (∃ h > (0 : ℝ),
      connectedComponentIn (H.cover ⁻¹' region) x = {p | h < p.val 2}) ∨
    (∃ c : EuclideanSpace ℝ (Fin 2), ∃ r > (0 : ℝ),
      connectedComponentIn (H.cover ⁻¹' region) x =
        {p | dist p.val (WithLp.toLp 2 ![c 0, c 1, r]) < r})

/-- A disjoint cusp neighborhood for every end, with compact complementary core. -/
structure CuspPacking {L : PolygonalLink} (H : HyperbolicStructure L) where
  /-- The cusp assigned to each link component. -/
  cusp : Fin L.components → Cusp H
  disjoint : Pairwise (fun i j ↦ Disjoint (cusp i).region (cusp j).region)
  compact_core : IsCompact ((⋃ i, (cusp i).region)ᶜ)

/-- The maximal total cusp volume `cv(L)` over all disjoint cusp packings. -/
def HyperbolicStructure.cuspVolume {L : PolygonalLink} (H : HyperbolicStructure L) : ℝ≥0∞ :=
  ⨆ P : CuspPacking H,
    @Measure.euclideanHausdorffMeasure L.complement
      (@MetricSpace.toEMetricSpace L.complement H.metric)
      (@borel L.complement H.metric.toUniformSpace.toTopologicalSpace)
      (@BorelSpace.mk L.complement H.metric.toUniformSpace.toTopologicalSpace
        (@borel L.complement H.metric.toUniformSpace.toTopologicalSpace) rfl)
      3 (⋃ i, (P.cusp i).region)

/-- The cusp-crossing density: maximal total cusp volume divided by crossing number
(Definition 1.4). -/
def HyperbolicStructure.cuspCrossingDensity {L : PolygonalLink}
    (H : HyperbolicStructure L) : ℝ :=
  H.cuspVolume.toReal / L.crossingNumber

/-- **Open question** (abstract; expected answer in the introduction). The number `3` is
the least upper bound of the cusp-crossing densities of all hyperbolic links.

No attainment and no density of values in `[0, 3]` is asserted. -/
theorem cusp_crossing_density_isLUB :
    IsLUB {r : ℝ | ∃ L : PolygonalLink, ∃ H : HyperbolicStructure L,
      r = H.cuspCrossingDensity} 3 := by
  sorry

end Adams2017Densities
