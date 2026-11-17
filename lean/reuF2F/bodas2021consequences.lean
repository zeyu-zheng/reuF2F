import Mathlib

/-!
# Consequences of the packing problem

Authors: Hrishikesh Bodas, Benjamin Drabkin, Caleb Fong, Su Jin, Justin Kim,
Wenxuan Li, Alexandra Seceleanu, Tingting Tang, and Brendan Williams.
Origin: [Polymath Jr. 2020](https://geometrynyc.wixsite.com/polymathreu).
Reference: H. Bodas, B. Drabkin, C. Fong, S. Jin, J. Kim, W. Li, A. Seceleanu, T. Tang, and
B. Williams, *Consequences of the packing problem*, J. Algebraic Combin. **54** (2021),
1095-1117; doi:10.1007/s10801-021-01039-5; arXiv:2101.04010.
-/

noncomputable section

namespace Bodas2021Consequences

open Finset

/-- A finite clutter: a hypergraph on the whole finite vertex type whose edge set is an
antichain under inclusion. -/
@[nolint unusedArguments]
def FiniteHypergraph (V : Type*) [Fintype V] :=
  {H : Hypergraph V // H.vertexSet = Set.univ ∧
    IsAntichain (fun s t : Set V ↦ s ⊆ t) H.edgeSet}

namespace FiniteHypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex cover of `H`: a set of vertices meeting every edge. -/
def IsVertexCover (H : FiniteHypergraph V) (C : Finset V) : Prop :=
  ∀ e ∈ H.val.edgeSet, ∃ v ∈ e, v ∈ C

/-- The transversal number `τ(H)`: the minimum cardinality of a vertex cover. -/
def transversalNumber (H : FiniteHypergraph V) : ℕ :=
  sInf {m : ℕ | ∃ C : Finset V, H.IsVertexCover C ∧ #C = m}

/-- An edge packing or matching: a set of pairwise-disjoint edges of `H`. -/
def IsEdgePacking (H : FiniteHypergraph V) (M : Finset (Set V)) : Prop :=
  (∀ e ∈ M, e ∈ H.val.edgeSet) ∧
    ∀ ⦃e₁ : Set V⦄, e₁ ∈ M → ∀ ⦃e₂ : Set V⦄, e₂ ∈ M → e₁ ≠ e₂ →
      ∀ v ∈ e₁, v ∈ e₂ → False

/-- The packing number `π(H)`: the maximum cardinality of an edge packing. -/
def packingNumber (H : FiniteHypergraph V) : ℕ :=
  sSup {m : ℕ | ∃ M : Finset (Set V), H.IsEdgePacking M ∧ #M = m}

/-- A König hypergraph: one satisfying `τ(H) = π(H)`. -/
def IsKonig (H : FiniteHypergraph V) : Prop :=
  H.transversalNumber = H.packingNumber

/-- The deletion-contraction minor, keeping only the inclusion-minimal edge images on the
surviving vertex type. -/
def minor (H : FiniteHypergraph V) (D C : Finset V) :
    FiniteHypergraph {v : V // v ∉ D ∧ v ∉ C} :=
  let images : Set (Set {v : V // v ∉ D ∧ v ∉ C}) :=
    (fun e : Set V ↦ Subtype.val ⁻¹' e) '' {e ∈ H.val.edgeSet | Disjoint e (D : Set V)}
  ⟨{ vertexSet := Set.univ
     edgeSet := {s ∈ images | ∀ t ∈ images, t ⊆ s → s ⊆ t}
     subset_vertexSet_of_mem_edgeSet' := fun _ _ ↦ Set.subset_univ _ },
   rfl, by
     intro s hs t ht hne hst
     exact hne (Set.Subset.antisymm hst (ht.2 s hs.1 hst))⟩

/-- The packing property: every deletion-contraction minor is König (Definition 2.14).
Minors with an empty edge (the unit ideal) are excluded, a convention not printed there. -/
def HasPackingProperty (H : FiniteHypergraph V) : Prop :=
  ∀ D C : Finset V, Disjoint D C →
    (∅ : Set {v : V // v ∉ D ∧ v ∉ C}) ∉ (H.minor D C).val.edgeSet →
      (H.minor D C).IsKonig

/-- The initial degree `alpha(I(H))` of the edge ideal. It is encoded as the least cardinality
of an edge. -/
def initialDegree (H : FiniteHypergraph V) : ℕ :=
  sInf {m : ℕ | ∃ e ∈ H.val.edgeSet, e.ncard = m}

/-- An `(a : b)`-rainbow coloring of `H`: each vertex receives a `b`-subset of `Fin a`, and
every edge sees every color. -/
def HasRainbowColoring (H : FiniteHypergraph V) (a b : ℕ) (color : V → Finset (Fin a)) : Prop :=
  (∀ v : V, #(color v) = b) ∧
    ∀ e ∈ H.val.edgeSet, ∀ i : Fin a, ∃ v ∈ e, i ∈ color v

/-- `(a : b)`-partite, also called `(a : b)`-rainbow colorable. -/
def IsPartite (H : FiniteHypergraph V) (a b : ℕ) : Prop :=
  ∃ color : V → Finset (Fin a), H.HasRainbowColoring a b color

/-- **Conjecture 5.8**. A clutter with the packing property is `(α(I) ht(I) : ht(I))`-partite.

The height is encoded as the transversal number; the target uses the nonempty, non-unit domain
and the minor convention above. -/
theorem conjecture_coloring (H : FiniteHypergraph V)
    (hedges : H.val.edgeSet.Nonempty) (hproper : (∅ : Set V) ∉ H.val.edgeSet)
    (hpack : H.HasPackingProperty) :
    H.IsPartite (H.initialDegree * H.transversalNumber) H.transversalNumber := by
  sorry

end FiniteHypergraph

end Bodas2021Consequences
