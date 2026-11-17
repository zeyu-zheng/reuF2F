import Mathlib

/-!
# Generalized bipyramids and hyperbolic volumes of alternating k-uniform tiling links

Authors: Colin Adams, Aaron Calderon, and Nathaniel Mayer.
Origin: [Williams College SMALL REU 2015](https://math.williams.edu/small/).
Reference: C. Adams, A. Calderon, and N. Mayer, *Generalized bipyramids and hyperbolic volumes of
alternating k-uniform tiling links*, Topology Appl. **271** (2020); arXiv:1709.00432v2.
-/

noncomputable section

namespace Adams2020Generalized

open Set Topology MeasureTheory
open scoped Real

universe u

/-- A compact connected Hausdorff second-countable surface without boundary, orientable or not. -/
structure ClosedSurface where
  /-- The underlying topological space of the surface. -/
  carrier : Type u
  [topology : TopologicalSpace carrier]
  [hausdorff : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
  [compact : CompactSpace carrier]
  [connected : ConnectedSpace carrier]
  [charts : ChartedSpace (Fin 2 → ℝ) carrier]

attribute [instance] ClosedSurface.topology ClosedSurface.hausdorff
  ClosedSurface.secondCountable ClosedSurface.compact ClosedSurface.connected
  ClosedSurface.charts

/-- The Euler characteristic, computed from singular homology in degrees `0`, `1` and `2` with
coefficients in `ZMod 2`. -/
def ClosedSurface.eulerCharacteristic (S : ClosedSurface.{u}) : ℤ :=
  let H := fun n ↦
    (((AlgebraicTopology.singularHomologyFunctor.{u} (ModuleCat.{u} (ZMod 2)) n).obj
      (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).obj (TopCat.of S.carrier))
  (Module.finrank (ZMod 2) (H 0) : ℤ) -
    (Module.finrank (ZMod 2) (H 1) : ℤ) +
    (Module.finrank (ZMod 2) (H 2) : ℤ)

/-- The truncated right-angled symmetric `n`-bipyramid in the Klein ball, with ideal regular
equatorial vertices and two truncated apexes. The source uses only `n ≥ 12`. -/
def rightAngledBipyramid (n : ℕ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  let a := π / (n : ℝ)
  let equator : Fin n → EuclideanSpace ℝ (Fin 3) := fun i ↦
    WithLp.toLp 2 ![Real.cos (2 * a * (i : ℕ)),
      Real.sin (2 * a * (i : ℕ)), 0]
  let top : EuclideanSpace ℝ (Fin 3) :=
    WithLp.toLp 2 ![0, 0, (Real.tan a)⁻¹]
  let bottom : EuclideanSpace ℝ (Fin 3) :=
    WithLp.toLp 2 ![0, 0, -(Real.tan a)⁻¹]
  {x | ‖x‖ < 1} ∩ convexHull ℝ (range equator ∪ {top, bottom}) ∩
    {x | |x 2| ≤ Real.tan a}

/-- A finite locally flat link in the interior of the product of a surface and an interval. -/
structure TameLink (S : Type*) [TopologicalSpace S] where
  /-- The number of link components. -/
  components : ℕ
  /-- The parametrisation of the components as embedded circles in `S × [0, 1]`. -/
  curve : C(Fin components × AddCircle (1 : ℝ), S × unitInterval)
  embedding : IsEmbedding curve
  interior : ∀ t, 0 < (curve t).2.val ∧ (curve t).2.val < 1
  locally_flat : ∀ t,
    ∃ e : OpenPartialHomeomorph (S × unitInterval) (EuclideanSpace ℝ (Fin 3)),
      curve t ∈ e.source ∧ e (curve t) = 0 ∧
      e '' (e.source ∩ range curve) = e.target ∩ {v | v 1 = 0 ∧ v 2 = 0}

/-- The set of points of the link. -/
def TameLink.carrier {S : Type*} [TopologicalSpace S] (L : TameLink S) : Set (S × unitInterval) :=
  range L.curve

/-- The complement of the link in `S × [0, 1]`, including both boundary surfaces. -/
abbrev TameLink.complement {S : Type*} [TopologicalSpace S] (L : TameLink S) :=
  {x : S × unitInterval | x ∉ L.carrier}

/-- A generic surface diagram: locally embedded branches, only finite transverse double points. -/
structure LinkDiagram (S : Type*) [TopologicalSpace S] extends TameLink S where
  locally_embedded_projection : ∀ t,
    ∃ U : Set (Fin components × AddCircle (1 : ℝ)), IsOpen U ∧ t ∈ U ∧
      IsEmbedding (fun z : U ↦ (curve z.val).1)
  at_most_double : ∀ q : S, {t | (curve t).1 = q}.encard ≤ 2
  finite_crossings : {q : S | ∃ a b, a ≠ b ∧ (curve a).1 = q ∧ (curve b).1 = q}.Finite
  transverse : ∀ a b, a ≠ b → (curve a).1 = (curve b).1 →
    ∃ e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)),
      (curve a).1 ∈ e.source ∧ e (curve a).1 = 0 ∧
      ∃ U V : Set (Fin components × AddCircle (1 : ℝ)),
        IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ b ∈ V ∧ Disjoint U V ∧
        IsEmbedding (fun z : U ↦ (curve z.val).1) ∧
        IsEmbedding (fun z : V ↦ (curve z.val).1) ∧
        (fun t ↦ (curve t).1) ⁻¹' e.source = U ∪ V ∧
        (fun t ↦ e (curve t).1) '' U = e.target ∩ {v | v 1 = 0} ∧
        (fun t ↦ e (curve t).1) '' V = e.target ∩ {v | v 0 = 0}

/-- Minimum generic crossing count on the same surface over the link's ambient isotopy class. -/
def TameLink.crossingNumber {S : Type*} [TopologicalSpace S] (L : TameLink S) : ℕ :=
  sInf {n | ∃ D : LinkDiagram S,
    ∃ H : unitInterval → ((S × unitInterval) ≃ₜ (S × unitInterval)),
      Continuous (fun p : unitInterval × (S × unitInterval) ↦ H p.1 p.2) ∧
      Continuous (fun p : unitInterval × (S × unitInterval) ↦ (H p.1).symm p.2) ∧
      H 0 = Homeomorph.refl (S × unitInterval) ∧
      H 1 '' L.carrier = D.toTameLink.carrier ∧
      {q : S | ∃ a b, a ≠ b ∧ (D.curve a).1 = q ∧ (D.curve b).1 = q}.encard = n}

/-- The closed side of a vertical geodesic plane in the L2 upper-half-space model. -/
abbrev hyperbolicHalfSpace :=
  {x : EuclideanSpace ℝ (Fin 3) | 0 < x 2 ∧ 0 ≤ x 0}

/-- A complete finite-volume hyperbolic structure on the link complement with both boundary
surfaces totally geodesic. -/
structure TGHyperbolicStructure {S : Type*} [TopologicalSpace S] (L : TameLink S) where
  /-- The hyperbolic metric on the link complement. -/
  metric : MetricSpace L.complement
  topology_eq : metric.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace L.complement)
  local_model : ∀ x : L.complement,
    ∃ e : OpenPartialHomeomorph L.complement hyperbolicHalfSpace,
      x ∈ e.source ∧
      (∀ y ∈ e.source,
        ((y.val.2.val = 0 ∨ y.val.2.val = 1) ↔ (e y).val 0 = 0)) ∧
      (∀ y ∈ e.source, ∀ z ∈ e.source,
        @dist L.complement metric.toDist y z =
          2 * Real.arsinh (dist (e y).val (e z).val /
            (2 * √((e y).val 2 * (e z).val 2))))
  complete : @CompleteSpace L.complement metric.toUniformSpace
  intrinsic :
    letI : TopologicalSpace L.complement := metric.toUniformSpace.toTopologicalSpace
    letI : MetricSpace L.complement := metric
    ∀ x y : L.complement,
      edist x y = ⨅ p : Path x y, eVariationOn p (univ : Set unitInterval)
  finite_volume :
    @Measure.euclideanHausdorffMeasure L.complement
      (@MetricSpace.toEMetricSpace L.complement metric)
      (@borel L.complement metric.toUniformSpace.toTopologicalSpace)
      (@BorelSpace.mk L.complement metric.toUniformSpace.toTopologicalSpace
        (@borel L.complement metric.toUniformSpace.toTopologicalSpace) rfl)
      3 (univ : Set L.complement) < ⊤

/-- Geometric hyperbolic volume, using Euclidean-normalized three-dimensional Hausdorff measure. -/
def TGHyperbolicStructure.volume {S : Type*} [TopologicalSpace S]
    {L : TameLink S} (H : TGHyperbolicStructure L) : ℝ :=
  (@Measure.euclideanHausdorffMeasure L.complement
    (@MetricSpace.toEMetricSpace L.complement H.metric)
    (@borel L.complement H.metric.toUniformSpace.toTopologicalSpace)
    (@BorelSpace.mk L.complement H.metric.toUniformSpace.toTopologicalSpace
      (@borel L.complement H.metric.toUniformSpace.toTopologicalSpace) rfl)
    3 (univ : Set L.complement)).toReal

/-- The source's volume density, with minimum crossing number on the fixed surface. -/
def TGHyperbolicStructure.volumeDensity {S : Type*} [TopologicalSpace S]
    {L : TameLink S} (H : TGHyperbolicStructure L) : ℝ :=
  H.volume / L.crossingNumber

/-- Klein coordinates on the hyperbolic plane, used to give actual geodesic polygon sides. -/
def kleinCoordinates (z : UpperHalfPlane) : EuclideanSpace ℝ (Fin 2) :=
  let d := z.re ^ 2 + z.im ^ 2 + 1
  WithLp.toLp 2 ![2 * z.re / d, (z.re ^ 2 + z.im ^ 2 - 1) / d]

/-- The regular right-angled n-gon in Klein coordinates, with geodesic sides
represented by Euclidean chords. The source range here is `n ≥ 12`. -/
def rightAngledPolygon (n : ℕ) : Polygon (EuclideanSpace ℝ (Fin 2)) n where
  vertices i :=
    let a := π / (n : ℝ)
    let r := √(1 - Real.tan a ^ 2)
    WithLp.toLp 2 ![r * Real.cos (2 * a * (i : ℕ)),
      r * Real.sin (2 * a * (i : ℕ))]

/-- An edge-to-edge regular right-angled hyperbolic polygon tiling and its surface quotient.
The covering and deck group allow orientation-reversing isometries. -/
structure RightAngledTiling (S : Type*) [TopologicalSpace S] (n : ℕ) where
  /-- The tiles of the tiling of the hyperbolic plane. -/
  tiles : Set (Set UpperHalfPlane)
  /-- An isometry placing the standard right-angled `n`-gon onto each tile. -/
  placement : tiles → (UpperHalfPlane ≃ᵢ UpperHalfPlane)
  tile_eq : ∀ P : tiles,
    P.val = placement P ''
      (kleinCoordinates ⁻¹' convexHull ℝ (range (rightAngledPolygon n).vertices))
  covers : ⋃₀ tiles = univ
  locally_finite : LocallyFinite (fun P : tiles ↦ P.val)
  disjoint_interiors : tiles.Pairwise (fun P Q ↦ Disjoint (interior P) (interior Q))
  edge_to_edge : ∀ P Q : tiles, P ≠ Q →
    P.val ∩ Q.val = ∅ ∨
    (∃ i j : Fin n,
      P.val ∩ Q.val = placement P ''
        (kleinCoordinates ⁻¹' {(rightAngledPolygon n).vertices i}) ∧
      P.val ∩ Q.val = placement Q ''
        (kleinCoordinates ⁻¹' {(rightAngledPolygon n).vertices j})) ∨
    (∃ i j : Fin n,
      P.val ∩ Q.val = placement P ''
        (kleinCoordinates ⁻¹' (rightAngledPolygon n).edgeSet ℝ i) ∧
      P.val ∩ Q.val = placement Q ''
        (kleinCoordinates ⁻¹' (rightAngledPolygon n).edgeSet ℝ j))
  /-- The covering map from the hyperbolic plane to the surface `S`. -/
  quotient : C(UpperHalfPlane, S)
  covering : IsCoveringMap quotient
  surjective : Function.Surjective quotient
  /-- The deck group of the covering, acting by isometries. -/
  deck : Subgroup (UpperHalfPlane ≃ᵢ UpperHalfPlane)
  fibers : ∀ x y, quotient x = quotient y ↔ ∃ g : deck, g.val x = y
  deck_preserves_tiles : ∀ (g : deck) P, P ∈ tiles → g.val '' P ∈ tiles
  finite_tile_orbits : ∃ F : Finset tiles,
    ∀ P : tiles, ∃ Q ∈ F, ∃ g : deck, P.val = g.val '' Q.val

/-- An alternating link whose projection is the edge skeleton of a quotient right-angled tiling. -/
structure TilingLink (S : Type*) [TopologicalSpace S] (n : ℕ) extends LinkDiagram S where
  /-- The right-angled tiling whose quotient edges form the link projection. -/
  tiling : RightAngledTiling S n
  projection_skeleton :
    range (fun t ↦ (curve t).1) = tiling.quotient '' (⋃ P ∈ tiling.tiles, frontier P)
  crossings_vertices :
    {q : S | ∃ a b, a ≠ b ∧ (curve a).1 = q ∧ (curve b).1 = q} =
      tiling.quotient ''
        (⋃ P : tiling.tiles, tiling.placement P ''
          (kleinCoordinates ⁻¹' range (rightAngledPolygon n).vertices))
  alternating : ∀ (i : Fin components) (a b : ℝ)
      (u v : Fin components × AddCircle (1 : ℝ)),
    a < b → b ≤ a + 1 →
    u ≠ (i, (a : AddCircle (1 : ℝ))) →
    v ≠ (i, (b : AddCircle (1 : ℝ))) →
    (curve u).1 = (curve (i, (a : AddCircle (1 : ℝ)))).1 →
    (curve v).1 = (curve (i, (b : AddCircle (1 : ℝ)))).1 →
    (∀ c : ℝ, a < c → c < b →
      ∀ t, (curve t).1 = (curve (i, (c : AddCircle (1 : ℝ)))).1 →
        t = (i, (c : AddCircle (1 : ℝ)))) →
    ((curve (i, (a : AddCircle (1 : ℝ)))).2.val < (curve u).2.val ↔
      (curve v).2.val < (curve (i, (b : AddCircle (1 : ℝ)))).2.val)

/-- **Conjecture 5.6**. At every fixed Euler genus, the sharp hyperbolic volume-density bound for
all links is attained by the stated nonorientable right-angled tiling family.

The index `m` is twice the source genus, including half-integral genera; the universal clause
covers surfaces of both orientation classes. -/
theorem fixed_genus_maximum (m : ℕ) (hm : 4 ≤ m) :
    let β : ℝ :=
      (∫⁻ x in rightAngledBipyramid (4 * m - 4),
        ENNReal.ofReal (((1 - ‖x‖ ^ 2) ^ 2)⁻¹)).toReal / ((m : ℝ) - 1)
    (∀ S : ClosedSurface,
      S.eulerCharacteristic = 2 - (m : ℤ) →
      ∀ (L : TameLink S.carrier) (H : TGHyperbolicStructure L),
        H.volumeDensity ≤ β) ∧
    (∃ S : ClosedSurface,
      S.eulerCharacteristic = 2 - (m : ℤ) ∧
      Module.rank ℚ
        ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) 2).obj
          (ModuleCat.of ℚ (ULift ℚ))).obj (TopCat.of S.carrier))) = 0 ∧
      ∃ L : TilingLink S.carrier (4 * m - 4),
      ∃ H : TGHyperbolicStructure L.toTameLink,
        H.volumeDensity = β) := by
  sorry

end Adams2020Generalized
