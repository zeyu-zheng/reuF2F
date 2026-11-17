import Mathlib

/-!
# Intrinsically projectively linked graphs

Authors: Joel Foisy, Luis Angel Topete Galvan, Evan Knowles, Uriel Alejandro Nolasco,
Yuanyuan Shen, and Lucy Wickham.
Origin: [SUNY Potsdam-Clarkson REU 2021](https://arxiv.org/pdf/2206.06877v1).
Reference: J. Foisy, L. A. Topete Galvan, E. Knowles, U. A. Nolasco, Y. Shen, and L. Wickham,
*Intrinsically projectively linked graphs*, preprint (2022), 29 pp.; arXiv:2206.06877.
-/

noncomputable section

namespace Foisy2022Intrinsically

open scoped Classical in
/-- The geometric realization of a finite graph in real coordinates, with the subtype topology. -/
abbrev GraphRealization {V : Type*} [Finite V] (G : SimpleGraph V) : Type _ :=
  {x : V → ℝ // x ∈ Finsupp.linearEquivFunOnFinite ℝ ℝ V ''
    (Geometry.SimplicialComplex.ofSimpleGraph G :
      Geometry.SimplicialComplex ℝ (V →₀ ℝ)).space}

/-- A finite graph minor, represented by disjoint connected nonempty branch sets. -/
def IsMinor {V W : Type*}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ branch : W → Set V,
    (∀ w, (G.induce (branch w)).Connected) ∧
    (∀ w₁ w₂, w₁ ≠ w₂ → Disjoint (branch w₁) (branch w₂)) ∧
    (∀ w₁ w₂, H.Adj w₁ w₂ →
      ∃ v₁ ∈ branch w₁, ∃ v₂ ∈ branch w₂, G.Adj v₁ v₂)

/-- The quotient topology on real projective space. -/
scoped instance projectivizationTopology (d : ℕ) :
    TopologicalSpace (Projectivization ℝ (Fin (d + 1) → ℝ)) := by
  unfold Projectivization
  infer_instance

/-- A PL embedding of a graph in real projective space. PL is encoded by finitely many affine
lifts to the antipodal polyhedral sphere. -/
structure PLGraphEmbedding {V : Type*} [Finite V] (G : SimpleGraph V) (d : ℕ) where
  /-- The underlying map from the graph realization to real projective space. -/
  toFun : GraphRealization G → Projectivization ℝ (Fin (d + 1) → ℝ)
  isEmbedding : Topology.IsEmbedding toFun
  piecewiseLinear : by
    classical
    exact ∀ u v, G.Adj u v →
      ∃ k > 0,
      ∃ t : Fin (k + 1) → ℝ,
        StrictMono t ∧ t 0 = 0 ∧ t (Fin.last k) = 1 ∧
        ∃ a : Fin k → AffineMap ℝ ℝ (Fin (d + 1) → ℝ),
          ∀ j : Fin k, ∀ r : ℝ,
            r ∈ Set.Icc (t j.castSucc) (t j.succ) →
            ∃ hn : a j r ≠ 0,
              (∑ i, |a j r i|) = 1 ∧
              ∃ x : GraphRealization G,
                x.val = (1 - r) • Pi.single u (1 : ℝ) + r • Pi.single v (1 : ℝ) ∧
                toFun x = Projectivization.mk ℝ (a j r) hn

/-- A split pair has one component in a topological 3-ball disjoint from the other. -/
def IsSplit (L₁ L₂ : Set (Projectivization ℝ (Fin 4 → ℝ))) : Prop :=
  ∃ A : Set (Projectivization ℝ (Fin 4 → ℝ)),
    Nonempty (A ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
      ((L₁ ⊆ A ∧ Disjoint L₂ A) ∨ (L₂ ⊆ A ∧ Disjoint L₁ A))

/-- **Unnumbered conjecture** (Section 3.7, p. 29). Adjoining a universal vertex to every
minor-minimal non-projective-planar graph gives an intrinsically projectively linked graph.

Proper minors exclude isomorphic copies, and PL maps are represented in the standard antipodal
polyhedral model. -/
theorem apex_obstruction_is_intrinsically_projectively_linked
    {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : ¬Nonempty (PLGraphEmbedding G 2))
    (hmin : ∀ (m : ℕ) (H : SimpleGraph (Fin m)),
      IsMinor H G → ¬Nonempty (H ≃g G) → Nonempty (PLGraphEmbedding H 2)) :
    let J := G.sum (⊥ : SimpleGraph Unit) ⊔ completeBipartiteGraph (Fin n) Unit
    ∀ f : PLGraphEmbedding J 3,
      ∃ u v, ∃ p : J.Walk u u, ∃ q : J.Walk v v,
          p.IsCycle ∧ q.IsCycle ∧
          Disjoint {x | x ∈ p.support} {x | x ∈ q.support} ∧
          let L₁ : Set (Projectivization ℝ (Fin 4 → ℝ)) :=
            f.toFun '' {x : GraphRealization J |
              ∃ e ∈ p.darts, ∃ r : ℝ,
                r ∈ Set.Icc 0 1 ∧
                x.val = (1 - r) • (Pi.single e.fst (1 : ℝ) : Fin n ⊕ Unit → ℝ) +
                  r • (Pi.single e.snd (1 : ℝ) : Fin n ⊕ Unit → ℝ)}
          let L₂ : Set (Projectivization ℝ (Fin 4 → ℝ)) :=
            f.toFun '' {x : GraphRealization J |
              ∃ e ∈ q.darts, ∃ r : ℝ,
                r ∈ Set.Icc 0 1 ∧
                x.val = (1 - r) • (Pi.single e.fst (1 : ℝ) : Fin n ⊕ Unit → ℝ) +
                  r • (Pi.single e.snd (1 : ℝ) : Fin n ⊕ Unit → ℝ)}
          ¬IsSplit L₁ L₂ := by
  sorry

end Foisy2022Intrinsically
