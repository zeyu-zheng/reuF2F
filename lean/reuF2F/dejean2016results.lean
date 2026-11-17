import Mathlib

/-!
# Some Results in the Theory of Elastic Networks

Authors: Bat Dejean and Christian Gorski.
Origin: [Indiana University Bloomington REU
2016](https://math.indiana.edu/undergraduate/reu-summer-research-program/past-reu/2016-projects.html).
Reference: B. Dejean and C. Gorski, *Some Results in the Theory of Elastic Networks*, Indiana REU
Research Reports (2016), 74--108.
-/

noncomputable section

namespace Dejean2016Results

/-- A finite marked elastic network, with positive resistance on each edge. -/
structure ElasticNetwork (n : ℕ) where
  /-- The number of vertices. -/
  vertexCount : ℕ
  /-- The number of edges. -/
  edgeCount : ℕ
  /-- The underlying finite graph on all vertices and edges. -/
  graph : Graph (Fin vertexCount) (Fin edgeCount)
  vertices : graph.vertexSet = Set.univ
  edges : graph.edgeSet = Set.univ
  /-- The `n` distinct marked vertices. -/
  marked : Fin n ↪ Fin vertexCount
  /-- The positive elasticity (resistance) of each edge. -/
  elasticity : Fin edgeCount → ℝ
  positive : ∀ e, 0 < elasticity e

/-- The Dirichlet energy of the geodesic extension of a vertex map. -/
def ElasticNetwork.dirichletEnergy {n : ℕ} (G : ElasticNetwork n)
    {X : Type*} [PseudoMetricSpace X] (f : Fin G.vertexCount → X) : ℝ :=
  ∑ e : Fin G.edgeCount,
    let h := (G.graph.edge_mem_iff_exists_isLink e).mp
      (by rw [G.edges]; exact Set.mem_univ e)
    let a := Classical.choose h
    let b := Classical.choose (Classical.choose_spec h)
    dist (f a) (f b) ^ 2 / G.elasticity e

/-- The Dirichlet energy of a marked homotopy class in a tree or real line. -/
def ElasticNetwork.harmonicEnergy {n : ℕ} (G : ElasticNetwork n)
    {X : Type*} [PseudoMetricSpace X] (boundary : Fin n → X) : ℝ :=
  sInf {E : ℝ | ∃ f : Fin G.vertexCount → X,
    (∀ i, f (G.marked i) = boundary i) ∧ E = G.dirichletEnergy f}

/-- Electrical equivalence, expressed through the boundary-voltage energy form. -/
def ElectricallyEquivalent {n : ℕ} (G H : ElasticNetwork n) : Prop :=
  ∀ boundary : Fin n → ℝ, G.harmonicEnergy boundary = H.harmonicEnergy boundary

/-- **Conjecture 6.1**. An elastic tree has no greater harmonic Dirichlet energy than any
electrically equivalent elastic graph, for every pipe-tree target.

Pipe trees are given by geodesic four-point metrics on finite vertex spans, zero-length edges
are collapsed, and harmonic energy is the Definition 1.3 infimum, not an attained minimum. -/
theorem trees_are_extremal
    {n : ℕ} (T G : ElasticNetwork n) [T.graph.Simple]
    (hT : T.graph.toSimpleGraph.IsTree) (h : ElectricallyEquivalent T G)
    {X : Type*} [MetricSpace X] [Nonempty X]
    (geodesic : ∀ x y : X, ∃ γ : ℝ → X,
      γ 0 = x ∧ γ (dist x y) = y ∧
      ∀ s ∈ Set.Icc (0 : ℝ) (dist x y),
        ∀ t ∈ Set.Icc (0 : ℝ) (dist x y),
          dist (γ s) (γ t) = |s - t|)
    (fourPoint : ∀ w x y z : X,
      dist w x + dist y z ≤
        max (dist w y + dist x z) (dist w z + dist x y))
    (boundary : Fin n → X) :
    T.harmonicEnergy boundary ≤ G.harmonicEnergy boundary := by
  sorry

end Dejean2016Results
