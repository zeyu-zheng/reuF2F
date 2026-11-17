import Mathlib

/-!
# Connectedness of the Free Uniform Spanning Forest as a function of edge weights

Authors: Marcell Alexy, Marton Borbenyi, Andras Imolay, and Adam Timar.
Origin: [Budapest REU Math Program 2020](https://reu.elte.hu/pastworkshops.html).
Reference: M. Alexy, M. Borbenyi, A. Imolay, and A. Timar, *Connectedness of the free uniform
spanning forest as a function of edge weights*, Electron. Commun. Probab. **27** (2022),
paper 13, 1-12; doi:10.1214/22-ECP453; arXiv:2011.12904v1.
-/

noncomputable section

namespace Alexy2022Connectedness

open MeasureTheory Filter SimpleGraph
open scoped Topology ENNReal

/-- The free uniform spanning forest law: the edge-cylinder limit of weighted spanning trees
along every connected finite induced exhaustion. A first clause requires some exhaustion to
exist, so the condition is not vacuous. -/
def IsFreeUniformSpanningForest {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (μ : ProbabilityMeasure (Set (Sym2 V))) : Prop := by
  classical
  exact
    (∃ K : ℕ → Finset V, Monotone K ∧
      (∀ n, (G.induce (K n : Set V)).Connected) ∧ ∀ v, ∃ n, v ∈ K n) ∧
    (∀ᵐ E ∂(μ : Measure (Set (Sym2 V))), E ⊆ G.edgeSet) ∧
    ∀ (K : ℕ → Finset V) (hK : Monotone K)
      (hc : ∀ n, (G.induce (K n : Set V)).Connected)
      (hcover : ∀ v, ∃ n, v ∈ K n) (A B : Finset (Sym2 V)),
      Tendsto (fun n ↦
        let F := G.induce (K n : Set V)
        let trees := ({J | J ≤ F ∧ J.IsTree} : Finset (SimpleGraph (K n)))
        let weight := fun J : SimpleGraph (K n) ↦
          ∏ e ∈ J.edgeFinset, c (Sym2.map Subtype.val e)
        (∑ J ∈ trees,
          if (A : Set (Sym2 V)) ⊆ (J.map Subtype.val).edgeSet ∧
              Disjoint (B : Set (Sym2 V)) (J.map Subtype.val).edgeSet
          then weight J else 0) / (∑ J ∈ trees, weight J))
        atTop (𝓝 ((μ : Measure (Set (Sym2 V))).real
          {E | (A : Set (Sym2 V)) ⊆ E ∧ Disjoint (B : Set (Sym2 V)) E}))

/-- The conductance: `w` inside each finite-factor copy and `1` on edges parallel to the tree
factor. Values on nonedges are unused. -/
def productConductance {V W : Type*} [DecidableEq V] (w : ℝ) :
    Sym2 (V × W) → ℝ :=
  Sym2.lift ⟨(fun a b ↦ if a.1 = b.1 then w else 1), by
    intro a b
    simp only [eq_comm]⟩

/-- **Conjecture 1.1**. Both connectivity phases are intervals, and an extended critical
conductance separates one component from infinitely many components.

The finite connected factor is arbitrary (no transitivity or regularity), and the regular tree
includes degree two. Almost-sure assertions hold separately for each weight; nothing is asserted
at the critical weight. -/
theorem conjecture_1_1 {V : Type*} [DecidableEq V] [Infinite V]
    (T : SimpleGraph V) [T.LocallyFinite] (hT : T.IsTree)
    (d : ℕ) (hd : T.IsRegularOfDegree d)
    {n : ℕ} (H : SimpleGraph (Fin n)) (hH : H.Connected)
    (μ : {w : ℝ // 0 < w} → ProbabilityMeasure (Set (Sym2 (V × Fin n))))
    (hμ : ∀ w, IsFreeUniformSpanningForest (T □ H)
      (productConductance w.val) (μ w)) :
    (∀ (a b : {w : ℝ // 0 < w}), a.val < b.val →
      (∀ᵐ E ∂(μ a : Measure (Set (Sym2 (V × Fin n)))),
        (SimpleGraph.fromEdgeSet E).Connected) →
      (∀ᵐ E ∂(μ b : Measure (Set (Sym2 (V × Fin n)))),
        (SimpleGraph.fromEdgeSet E).Connected) →
      ∀ (w : {w : ℝ // 0 < w}), a.val ≤ w.val → w.val ≤ b.val →
        ∀ᵐ E ∂(μ w : Measure (Set (Sym2 (V × Fin n)))),
          (SimpleGraph.fromEdgeSet E).Connected) ∧
    (∀ (a b : {w : ℝ // 0 < w}), a.val < b.val →
      (∀ᵐ E ∂(μ a : Measure (Set (Sym2 (V × Fin n)))),
        ¬(SimpleGraph.fromEdgeSet E).Connected) →
      (∀ᵐ E ∂(μ b : Measure (Set (Sym2 (V × Fin n)))),
        ¬(SimpleGraph.fromEdgeSet E).Connected) →
      ∀ (w : {w : ℝ // 0 < w}), a.val ≤ w.val → w.val ≤ b.val →
        ∀ᵐ E ∂(μ w : Measure (Set (Sym2 (V × Fin n)))),
          ¬(SimpleGraph.fromEdgeSet E).Connected) ∧
    ∃ γ : ℝ≥0∞, ∀ (w : {w : ℝ // 0 < w}),
      (γ < ENNReal.ofReal w.val →
        ∀ᵐ E ∂(μ w : Measure (Set (Sym2 (V × Fin n)))),
          (SimpleGraph.fromEdgeSet E).Connected) ∧
      (ENNReal.ofReal w.val < γ →
        ∀ᵐ E ∂(μ w : Measure (Set (Sym2 (V × Fin n)))),
          Infinite (SimpleGraph.fromEdgeSet E).ConnectedComponent) := by
  sorry

end Alexy2022Connectedness
