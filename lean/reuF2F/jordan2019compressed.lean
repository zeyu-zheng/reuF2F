import Mathlib

/-!
# Compressed frameworks and compressible graphs

Authors: Tibor Jordan and Jialin Zhang.
Origin: [Budapest Semesters in Mathematics](https://www.bsmath.hu/articles.html).
Reference: T. Jordan and J. Zhang, *Compressed frameworks and compressible graphs*, Proc. 11th
Hungarian-Japanese Symposium on Discrete Mathematics and its Applications (Tokyo, 2019),
189-198; expanded version, EGRES Technical Report 2019-10.
-/

noncomputable section

namespace Jordan2019Compressed

/-- All vertex coordinates are algebraically independent over the rationals (Section 1). -/
def IsGeneric {V : Type*} (p : V → EuclideanSpace ℝ (Fin 2)) : Prop :=
  AlgebraicIndependent ℚ (fun i : V × Fin 2 ↦ p i.1 i.2)

open scoped Classical in
/-- The planar rigidity matrix: the row of an edge has the coordinate differences in its two
endpoint blocks and zeros elsewhere (Section 6). -/
def rigidityMatrix {V : Type*} (p : V → EuclideanSpace ℝ (Fin 2)) :
    Matrix (Sym2 V) (V × Fin 2) ℝ :=
  Sym2.lift ⟨fun u v i ↦
    (if i.1 = u then p u i.2 - p v i.2 else 0) +
    (if i.1 = v then p v i.2 - p u i.2 else 0),
    fun u v ↦ by funext i; exact add_comm _ _⟩

/-- A circuit of the rigidity matrix is a minimally linearly dependent set of rows. -/
def IsRigidityCircuit {V : Type*} (p : V → EuclideanSpace ℝ (Fin 2))
    (C : Set (Sym2 V)) : Prop :=
  ¬LinearIndependent ℝ (fun e : C ↦ rigidityMatrix p e.val) ∧
    ∀ D ⊂ C, LinearIndependent ℝ (fun e : D ↦ rigidityMatrix p e.val)

/-- M-connectivity: at least two edges, no isolated vertices, and every pair of distinct edges
in a common generic rigidity circuit (Section 6; Jackson--Jordan (2005), Section 3). -/
def MConnected {V : Type*} (G : SimpleGraph V) : Prop :=
  (∀ v, ∃ w, G.Adj v w) ∧
  (∃ e ∈ G.edgeSet, ∃ f ∈ G.edgeSet, e ≠ f) ∧
  ∃ p : V → EuclideanSpace ℝ (Fin 2), IsGeneric p ∧
    ∀ e ∈ G.edgeSet, ∀ f ∈ G.edgeSet, e ≠ f →
      ∃ C ⊆ G.edgeSet, e ∈ C ∧ f ∈ C ∧ IsRigidityCircuit p C

/-- A generic planar realization in which every pairwise distance is minimal among all
realizations with the same edge lengths (Section 1). -/
def GenericallyCompressible {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ p : V → EuclideanSpace ℝ (Fin 2), IsGeneric p ∧
    (∀ u v, G.Adj u v → p u ≠ p v) ∧
    ∀ q : V → EuclideanSpace ℝ (Fin 2),
      (∀ u v, G.Adj u v → dist (p u) (p v) = dist (q u) (q v)) →
      ∀ u v, dist (p u) (p v) ≤ dist (q u) (q v)

/-- The cut-pair relation (Section 3). Vertices in no cut-pair are kept as isolated vertices;
the target restricts to incident vertices. -/
def cutPairGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ¬(G.induce {w | w ≠ u ∧ w ≠ v}).Connected
  symm := by
    constructor
    intro u v h
    refine ⟨Ne.symm h.1, ?_⟩
    have hs : {w : V | w ≠ v ∧ w ≠ u} = {w : V | w ≠ u ∧ w ≠ v} := by
      ext w
      exact and_comm
    rw [hs]
    exact h.2
  loopless := by constructor; intro u h; exact h.1 rfl

/-- **Conjecture 21** (expanded report: Conjecture 22). An M-connected graph has a compressed
generic planar realization exactly when its cut-pair graph is a cycle or a disjoint union of
paths, including the empty union. -/
theorem conjecture_21 {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : MConnected G) :
    GenericallyCompressible G ↔
      let B := (cutPairGraph G).induce {v | ∃ w, (cutPairGraph G).Adj v w}
      (∃ n ≥ 3, Nonempty (B ≃g SimpleGraph.cycleGraph n)) ∨
        (∀ c : B.ConnectedComponent,
          ∃ n : ℕ, Nonempty (c.toSimpleGraph ≃g SimpleGraph.pathGraph (n + 1))) := by
  sorry

end Jordan2019Compressed
