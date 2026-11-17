import Mathlib

/-!
# Finite cobordism

Author: Samuel Coyle.
Origin: [University of Chicago REU 2025](https://math.uchicago.edu/~may/REU2025/).
Reference: S. Coyle, *Finite cobordism*, University of Chicago REU research report (2025), 28 pp.
-/

noncomputable section

namespace Coyle2025Finite

open Finset

universe u

/-- The source finite-space topology has precisely the lower sets as its open sets. -/
instance finiteSpaceTopology (P : FinPartOrd.{u}) : TopologicalSpace P :=
  Topology.lowerSet P

/-- The strict upper set of an up-beat point has a least element (Definition 2.7). -/
def IsUpBeat {P : FinPartOrd.{u}} (x : P) : Prop :=
  ∃ y : P, IsLeast (Set.Ioi x) y

/-- All points below an up-beat point (Definition 3.1). -/
def upBoundary (P : FinPartOrd.{u}) : Set P :=
  {x | ∃ y : P, IsUpBeat y ∧ x ≤ y}

open scoped Classical in
/-- The subdivision by nonempty chains ordered by inclusion (Theorem 2.10). -/
def Sd (P : FinPartOrd.{u}) : FinPartOrd.{u} :=
  FinPartOrd.of {s : Finset P // s.Nonempty ∧ IsChain (· ≤ ·) (s : Set P)}

/-- Barystability as an equality of induced subspaces in `Sd(P)` (Definition 3.8). -/
def Barystable (P : FinPartOrd.{u}) : Prop :=
  upBoundary (Sd P) = {s | (s.val : Set P) ⊆ upBoundary P}

/-- The largest chain has `n + 1` points and every maximal chain has that size (Definition 3.15
and Section 3.3). Maximal means inclusion-maximal, not saturated. -/
def HomogeneousHeight (n : ℕ) (P : FinPartOrd.{u}) : Prop :=
  (Set.univ : Set P).chainHeight (· ≤ ·) = (n + 1 : ENat) ∧
    ∀ s : Finset P, IsMaxChain (· ≤ ·) (s : Set P) → #s = n + 1

/-- The class `BStab_n`, which includes the empty finite space (Section 4). -/
def BStab (n : ℕ) (P : FinPartOrd.{u}) : Prop :=
  IsEmpty P ∨ (Barystable P ∧ HomogeneousHeight n P)

/-- Closedness in the source sense: empty up-boundary, not topological closedness. -/
def Closed (P : FinPartOrd.{u}) : Prop :=
  upBoundary P = ∅

/-- A weak point: its strict lower or strict upper finite subspace is contractible (p. 5). -/
def IsWeakPoint {P : FinPartOrd.{u}} (x : P) : Prop :=
  ContractibleSpace {y : P // y < x} ∨ ContractibleSpace {y : P // x < y}

set_option genInjectivity false in
set_option genCtorIdx false in
set_option genSizeOf false in
/-- An arbitrary finite ambient poset with the same pointwise incoming marking. -/
structure MarkedFiniteSpace (X : FinPartOrd.{u}) where
  /-- The ambient finite poset. -/
  space : FinPartOrd.{u}
  /-- The order embedding marking `X` inside the ambient poset. -/
  mark : X ↪o space

open scoped Classical in
/-- Delete one unmarked point, retaining the original marking pointwise. -/
def MarkedFiniteSpace.delete {X : FinPartOrd.{u}} (M : MarkedFiniteSpace X)
    (p : M.space) (away : ∀ x : X, M.mark x ≠ p) : MarkedFiniteSpace X where
  space := FinPartOrd.of {y : M.space // y ≠ p}
  mark :=
    { toFun := fun x ↦ ⟨M.mark x, away x⟩
      inj' := fun _ _ h ↦ M.mark.injective (congrArg Subtype.val h)
      map_rel_iff' := M.mark.map_rel_iff }

/-- The generators of the fixed-incoming relative weak-point relation (pp. 23--24). -/
inductive RelativeMove (X : FinPartOrd.{u}) :
    MarkedFiniteSpace X → MarkedFiniteSpace X → Prop
  | delete (M : MarkedFiniteSpace X) (p : M.space)
      (away : ∀ x : X, M.mark x ≠ p) (hp : IsWeakPoint p) :
      RelativeMove X M (M.delete p away)
  | rename (M N : MarkedFiniteSpace X) (e : M.space ≃o N.space)
      (fixed : ∀ x : X, e (M.mark x) = N.mark x) :
      RelativeMove X M N

set_option genInjectivity false in
set_option genCtorIdx false in
set_option genSizeOf false in
/-- A finite cobordism with its boundary identification (Definition 4.1). The w-cobordism
condition is the separate structure `WCobordism`. -/
structure FiniteCobordism (n : ℕ) (X : FinPartOrd.{u}) where
  /-- The outgoing boundary poset. -/
  outgoing : FinPartOrd.{u}
  /-- The finite poset forming the cobordism. -/
  space : FinPartOrd.{u}
  incoming_bstab : BStab n X
  incoming_closed : Closed X
  outgoing_bstab : BStab n outgoing
  outgoing_closed : Closed outgoing
  space_bstab : BStab (n + 1) space
  /-- The identification of the incoming and outgoing posets with the up-boundary. -/
  boundary : (X ⊕ outgoing) ≃o {x : space // x ∈ upBoundary space}

/-- The incoming inclusion obtained from this cobordism's boundary isomorphism. -/
def FiniteCobordism.incoming {n : ℕ} {X : FinPartOrd.{u}}
    (C : FiniteCobordism n X) : X ↪o C.space where
  toFun x := (C.boundary (Sum.inl x)).val
  inj' := by
    intro x y h
    exact Sum.inl_injective (C.boundary.injective (Subtype.ext h))
  map_rel_iff' := by
    intro x y
    change C.boundary (Sum.inl x) ≤ C.boundary (Sum.inl y) ↔ x ≤ y
    exact C.boundary.map_rel_iff.trans Sum.inl_le_inl_iff

/-- The outgoing inclusion obtained from the same boundary isomorphism. -/
def FiniteCobordism.outgoingInclusion {n : ℕ} {X : FinPartOrd.{u}}
    (C : FiniteCobordism n X) : C.outgoing ↪o C.space where
  toFun y := (C.boundary (Sum.inr y)).val
  inj' := by
    intro x y h
    exact Sum.inr_injective (C.boundary.injective (Subtype.ext h))
  map_rel_iff' := by
    intro x y
    change C.boundary (Sum.inr x) ≤ C.boundary (Sum.inr y) ↔ x ≤ y
    exact C.boundary.map_rel_iff.trans Sum.inr_le_inr_iff

/-- The incoming marked pair of a cobordism. -/
def FiniteCobordism.marked {n : ℕ} {X : FinPartOrd.{u}}
    (C : FiniteCobordism n X) : MarkedFiniteSpace X where
  space := C.space
  mark := C.incoming

open Set Convexity

/-- The source order complex: nonempty chains of a finite ordered space. -/
def orderComplex (P : Type*) [PartialOrder P] : AbstractSimplicialComplex P where
  faces := {s | s.Nonempty ∧ IsChain (· ≤ ·) (s : Set P)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, hs.2.mono (by simpa using hts)⟩
  singleton_mem p := by
    simp

/-- The geometric realization by standard-simplex weights supported on a face. -/
def realization {P : Type*} (K : PreAbstractSimplicialComplex P) :
    Set (StdSimplex ℝ P) :=
  {w | w.weights.support ∈ K}

open scoped Classical in
/-- The affine realization of a vertex map that takes faces to faces. -/
def realizationMap {P Q : Type*} (K : PreAbstractSimplicialComplex P)
    (L : PreAbstractSimplicialComplex Q) (f : P → Q)
    (hf : ∀ s ∈ K, s.image f ∈ L) : C(realization K, realization L) where
  toFun w := ⟨StdSimplex.map f w.val, by
    apply (L.isRelLowerSet_faces (hf _ w.property)).2
    · exact Finsupp.mapDomain_support
    · exact StdSimplex.support_weights_nonempty _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (StdSimplex.continuous_map ℝ f).comp continuous_subtype_val

open scoped Classical in
/-- The realization of a monotone map on the source finite-space order complexes. -/
def orderRealizationMap {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) :
    C(realization (orderComplex P).toPreAbstractSimplicialComplex,
      realization (orderComplex Q).toPreAbstractSimplicialComplex) :=
  realizationMap _ _ f (by
    intro s hs
    refine ⟨hs.1.image _, ?_⟩
    simpa only [Finset.coe_image] using f.monotone.isChain_image hs.2)

open Topology

set_option autoImplicit false

set_option genInjectivity false in
set_option genCtorIdx false in
set_option genSizeOf false in
/-- A finite Hausdorff CW complex with its underlying space and Mathlib characteristic maps. -/
structure FiniteCW where
  /-- The underlying space of the CW complex. -/
  Carrier : Type u
  [topology : TopologicalSpace Carrier]
  [hausdorff : T2Space Carrier]
  [cw : CWComplex (Set.univ : Set Carrier)]
  [finite : CWComplex.Finite (Set.univ : Set Carrier)]

attribute [instance] FiniteCW.topology FiniteCW.hausdorff FiniteCW.cw FiniteCW.finite

set_option genInjectivity false in
set_option genCtorIdx false in
set_option genSizeOf false in
/-- A CW identification with a subcomplex: a homeomorphism onto it preserving open cells
dimension by dimension. -/
structure CWSubcomplexEmbedding (X Y : FiniteCW.{u}) where
  /-- The subcomplex of `Y` onto which `X` is identified. -/
  image : CWComplex.Subcomplex (Set.univ : Set Y.Carrier)
  /-- The homeomorphism from `X` onto the subcomplex. -/
  homeomorph : X.Carrier ≃ₜ image
  /-- The bijection between the `n`-cells of `X` and those of the subcomplex. -/
  cells (n : ℕ) : RelCWComplex.cell (Set.univ : Set X.Carrier) n ≃ image.I n
  open_cells (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X.Carrier) n) :
    (fun x ↦ (homeomorph x).val) '' CWComplex.openCell n i =
      CWComplex.openCell n (cells n i).val

/-- The actual map into the ambient space, not an independently chosen map. -/
def CWSubcomplexEmbedding.inclusion {X Y : FiniteCW.{u}}
    (j : CWSubcomplexEmbedding X Y) : C(X.Carrier, Y.Carrier) where
  toFun x := (j.homeomorph x).val
  continuous_toFun := continuous_subtype_val.comp j.homeomorph.continuous

set_option genInjectivity false in
set_option genCtorIdx false in
set_option genSizeOf false in
/-- A characteristic map for a specified CW cell, not necessarily the one stored in the CW
structure. The ball is Mathlib's maximum-norm ball, a cube. -/
structure CWCharacteristicMap (X : FiniteCW.{u}) (n : ℕ)
    (i : RelCWComplex.cell (Set.univ : Set X.Carrier) n) where
  /-- The characteristic map from the open unit ball onto the open cell. -/
  map : PartialEquiv (Fin n → ℝ) X.Carrier
  source_eq : map.source = Metric.ball 0 1
  target_eq : map.target = CWComplex.openCell n i
  continuousOn : ContinuousOn map (Metric.closedBall 0 1)
  continuousOn_symm : ContinuousOn map.symm map.target
  boundary : Set.MapsTo map (Metric.sphere 0 1)
    (CWComplex.skeletonLT (Set.univ : Set X.Carrier) n)

set_option genInjectivity false in
set_option genCtorIdx false in
set_option genSizeOf false in
/-- A CW pair over a fixed, pointwise marked incoming CW complex. -/
structure MarkedCWPair (A : FiniteCW.{u}) where
  /-- The ambient finite CW complex. -/
  space : FiniteCW.{u}
  /-- The identification of the incoming complex `A` with a subcomplex. -/
  incoming : CWSubcomplexEmbedding A space

set_option genInjectivity false in
set_option genCtorIdx false in
set_option genSizeOf false in
/-- A CW isomorphism relative to the incoming marking (Cohen 5.2). It preserves cells but not
necessarily the chosen parametrizations. -/
structure RelativeCWIsomorphism {A : FiniteCW.{u}} (P Q : MarkedCWPair A) where
  /-- The underlying homeomorphism of ambient spaces. -/
  homeomorph : P.space.Carrier ≃ₜ Q.space.Carrier
  /-- The induced bijection between `n`-cells. -/
  cells (n : ℕ) :
    RelCWComplex.cell (Set.univ : Set P.space.Carrier) n ≃
      RelCWComplex.cell (Set.univ : Set Q.space.Carrier) n
  open_cells (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set P.space.Carrier) n) :
    homeomorph '' CWComplex.openCell n i = CWComplex.openCell n (cells n i)
  relative (a : A.Carrier) :
    homeomorph (P.incoming.inclusion a) = Q.incoming.inclusion a

set_option genInjectivity false in
set_option genCtorIdx false in
set_option genSizeOf false in
/-- An elementary expansion relative to `A` (Cohen Section 4). Cohen's ball pair is modelled by a
cube whose free face is the first-coordinate `+1` face, via `Fin.cons 1`. -/
structure RelativeCWExpansion {A : FiniteCW.{u}} (P Q : MarkedCWPair A) where
  /-- The identification of the smaller complex with a subcomplex of the larger. -/
  old : CWSubcomplexEmbedding P.space Q.space
  relative (a : A.Carrier) :
    old.inclusion (P.incoming.inclusion a) = Q.incoming.inclusion a
  /-- The dimension `n` of the adjoined free face. -/
  dimension : ℕ
  /-- The adjoined `n`-cell. -/
  face : RelCWComplex.cell (Set.univ : Set Q.space.Carrier) dimension
  /-- The adjoined `(n + 1)`-cell. -/
  coface : RelCWComplex.cell (Set.univ : Set Q.space.Carrier) (dimension + 1)
  face_new : ¬old.image.I dimension face
  coface_new : ¬old.image.I (dimension + 1) coface
  adjoining : (Set.univ : Set Q.space.Carrier) =
    (old.image : Set Q.space.Carrier) ∪
      (CWComplex.openCell dimension face ∪ CWComplex.openCell (dimension + 1) coface)
  /-- The characteristic map of the adjoined `(n + 1)`-cell. -/
  characteristic : CWCharacteristicMap Q.space (dimension + 1) coface
  /-- The characteristic map of the adjoined `n`-cell. -/
  faceCharacteristic : CWCharacteristicMap Q.space dimension face
  on_face (x : Fin dimension → ℝ) (hx : x ∈ Metric.closedBall 0 1) :
    characteristic.map (Fin.cons 1 x) = faceCharacteristic.map x
  on_complement : Set.MapsTo characteristic.map
    (closure (Metric.sphere (0 : Fin (dimension + 1) → ℝ) 1 \ {x | x 0 = 1}))
    (old.inclusion ''
      CWComplex.skeletonLT (Set.univ : Set P.space.Carrier) (dimension + 1))

/-- A finite formal CW deformation relative to the marked base. Collapses are reverse expansions
in the equivalence closure, which also includes relative CW renaming. -/
def FormalCWDeformation {A : FiniteCW.{u}} (P Q : MarkedCWPair A) : Prop :=
  Relation.EqvGen (fun B C : MarkedCWPair A ↦
    Nonempty (RelativeCWExpansion B C) ∨ Nonempty (RelativeCWIsomorphism B C)) P Q

set_option genInjectivity false in
set_option genCtorIdx false in
set_option genSizeOf false in
/-- A homotopically trivial CW pair (Cohen Section 6). -/
structure HomotopicallyTrivialCWPair (A : FiniteCW.{u}) extends MarkedCWPair A where
  inclusion_equivalence : ∃ e : ContinuousMap.HomotopyEquiv A.Carrier space.Carrier,
    e.toFun = incoming.inclusion

set_option genInjectivity false in
set_option genCtorIdx false in
set_option genSizeOf false in
/-- A w-cobordism: both boundary inclusions realize to weak homotopy equivalences
(Definition 4.1). -/
structure WCobordism (n : ℕ) (X : FinPartOrd.{u}) where
  /-- The underlying finite cobordism. -/
  data : FiniteCobordism n X
  incoming_equivalence : ∃ e : ContinuousMap.HomotopyEquiv
    (realization (orderComplex X).toPreAbstractSimplicialComplex)
    (realization (orderComplex data.space).toPreAbstractSimplicialComplex),
    e.toFun = orderRealizationMap data.incoming.toOrderHom
  outgoing_equivalence : ∃ e : ContinuousMap.HomotopyEquiv
    (realization (orderComplex data.outgoing).toPreAbstractSimplicialComplex)
    (realization (orderComplex data.space).toPreAbstractSimplicialComplex),
    e.toFun = orderRealizationMap data.outgoingInclusion.toOrderHom

set_option genInjectivity false in
set_option genCtorIdx false in
set_option genSizeOf false in
/-- The canonical chain-cell structure on the order-complex realization, as a finite CW
complex. -/
structure CanonicalCWRealization (P : FinPartOrd.{u}) where
  /-- The finite CW complex realizing the order complex. -/
  complex : FiniteCW.{u}
  /-- The homeomorphism from the order-complex realization to the CW complex. -/
  identify :
    realization (orderComplex P).toPreAbstractSimplicialComplex ≃ₜ complex.Carrier
  /-- The bijection between chains with `n + 1` elements and `n`-cells. -/
  cells (n : ℕ) :
    {s : Finset P // s ∈ orderComplex P ∧ #s = n + 1} ≃
      RelCWComplex.cell (Set.univ : Set complex.Carrier) n
  open_cells (n : ℕ) (s : {s : Finset P // s ∈ orderComplex P ∧ #s = n + 1}) :
    identify '' {w | w.val.weights.support = s.val} =
      CWComplex.openCell n (cells n s)

set_option genInjectivity false in
set_option genCtorIdx false in
set_option genSizeOf false in
/-- A canonical CW witness for the realized marked cobordism pair. -/
structure CanonicalCWPairRealization {n : ℕ} {X : FinPartOrd.{u}}
    (A : CanonicalCWRealization X) (C : WCobordism n X) where
  /-- The homotopically trivial CW pair realizing the cobordism. -/
  pair : HomotopicallyTrivialCWPair A.complex
  /-- The homeomorphism from the cobordism's order-complex realization to the pair. -/
  identify :
    realization (orderComplex C.data.space).toPreAbstractSimplicialComplex ≃ₜ
      pair.space.Carrier
  /-- The bijection between chains with `k + 1` elements and `k`-cells. -/
  cells (k : ℕ) :
    {s : Finset C.data.space // s ∈ orderComplex C.data.space ∧ #s = k + 1} ≃
      RelCWComplex.cell (Set.univ : Set pair.space.Carrier) k
  open_cells (k : ℕ)
      (s : {s : Finset C.data.space // s ∈ orderComplex C.data.space ∧ #s = k + 1}) :
    identify '' {w | w.val.weights.support = s.val} =
      CWComplex.openCell k (cells k s)
  incoming (x : realization (orderComplex X).toPreAbstractSimplicialComplex) :
    identify (orderRealizationMap C.data.incoming.toOrderHom x) =
      pair.incoming.inclusion (A.identify x)

/-- **Conjecture 5.4** (p. 24). The incoming-torsion correspondence classifies all finite
w-cobordisms relative to the incoming boundary, uniformly in sufficiently large dimensions.

Cohen's CW-pair carrier represents componentwise Whitehead values (Theorem 21.1), and pair
torsion is map torsion transported to the incoming space; the correspondence is stated as a graph
(totality, uniqueness, descent, surjectivity and injectivity for the weak-point relation), with
intermediates not required to be cobordisms and empty or disconnected endpoints retained. -/
theorem conjecture_5_4 :
    ∃ N : ℕ, ∀ n ≥ N, ∀ X : FinPartOrd.{u},
      BStab n X → Closed X →
      Nonempty (CanonicalCWRealization X) ∧
      ∀ A : CanonicalCWRealization X,
        let G := fun (d : WCobordism n X) (c : HomotopicallyTrivialCWPair A.complex) ↦
          ∃ b : CanonicalCWPairRealization A d,
            FormalCWDeformation b.pair.toMarkedCWPair c.toMarkedCWPair
        (∀ d : WCobordism n X, ∃ c, G d c) ∧
        (∀ (d : WCobordism n X) c c', G d c → G d c' →
          FormalCWDeformation c.toMarkedCWPair c'.toMarkedCWPair) ∧
        (∀ d e : WCobordism n X,
          Relation.EqvGen (RelativeMove X) d.data.marked e.data.marked →
            ∀ c, G d c ↔ G e c) ∧
        (∀ c : HomotopicallyTrivialCWPair A.complex, ∃ d, G d c) ∧
        (∀ (d e : WCobordism n X) c c', G d c → G e c' →
          FormalCWDeformation c.toMarkedCWPair c'.toMarkedCWPair →
            Relation.EqvGen (RelativeMove X) d.data.marked e.data.marked) := by
  sorry

end Coyle2025Finite
