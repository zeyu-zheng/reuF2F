import Mathlib

/-!
# On the subgraph query problem

Authors: Ryan Alweiss, Chady Ben Hamida, Xiaoyu He, and Alexander Moreira.
Origin: [Stanford SURIM
2019](https://surim.stanford.edu/publications/combinatorics/query-complexity-degenerate-graphs).
Reference: R. Alweiss, C. Ben Hamida, X. He, and A. Moreira, *On the subgraph query problem*,
Combin. Probab. Comput. **30** (2021), 1-16; doi:10.1017/S0963548320000218; arXiv:1911.04413v2.
-/

noncomputable section

namespace Alweiss2021Subgraph

open SimpleGraph
open scoped Topology
open Finset

open scoped Classical in
/-- A graph is `d`-degenerate when every nonempty induced subgraph has a
vertex of degree at most `d` (Section 1). -/
def IsDegenerate {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → ∃ v, ∃ hv : v ∈ S,
    (G.induce (fun w ↦ w ∈ S)).degree ⟨v, hv⟩ ≤ d

/-- A `(1,1)`-degenerate partition: an ordered partition into induced trees, each of whose
vertices has at most one neighbor in earlier trees (Section 5). -/
def IsOneDegeneratePartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ k : ℕ, ∃ T : Fin k → Finset V,
    (∀ i, (T i).Nonempty ∧ (G.induce (fun v ↦ v ∈ T i)).IsTree) ∧
    (∀ v : V, ∃ i, v ∈ T i) ∧
    (∀ i j : Fin k, i ≠ j → Disjoint (T i) (T j)) ∧
    ∀ i : Fin k, ∀ v ∈ T i,
      #({w | G.Adj v w ∧ ∃ j : Fin k, j < i ∧ w ∈ T j} : Finset V) ≤ 1

/-- Finite adaptive adjacency-query strategies on `N` vertex labels. A bounded strategy on
`G(∞, p)` uses only finitely many labels, so `Fin N` suffices. -/
inductive AdaptiveQueryTree (N : ℕ) where
  | done : AdaptiveQueryTree N
  | query (u v : Fin N) (hne : u ≠ v)
      (absent present : AdaptiveQueryTree N) : AdaptiveQueryTree N

namespace AdaptiveQueryTree

open scoped Classical in
/-- The queried unordered edges along the path selected by `G`. -/
def queriesOn {N : ℕ} : AdaptiveQueryTree N → SimpleGraph (Fin N) →
    Finset (Sym2 (Fin N))
  | done, _ => ∅
  | query u v _ absent present, G =>
      insert s(u, v) (if G.Adj u v then present.queriesOn G else absent.queriesOn G)

/-- The worst-case query budget, including repeated queries if a strategy makes them. -/
def queryCount {N : ℕ} : AdaptiveQueryTree N → ℕ
  | done => 0
  | query _ _ _ absent present => 1 + max absent.queryCount present.queryCount

end AdaptiveQueryTree

/-- The query complexity `f(H, p)`: the least worst-case budget that finds a copy of `H` with
probability at least `1 / 2` (Section 1). A copy must lie in the revealed edges, and the
feasible set is nonempty for `0 < p ≤ 1`. -/
def adaptiveSubgraphQueryCost {V : Type*}
    (H : SimpleGraph V) (p : ℝ) (hp : 0 < p ∧ p ≤ 1) : ℝ :=
  sInf {q : ℝ | ∃ N : ℕ, ∃ T : AdaptiveQueryTree N,
    (1 / 2 : ℝ) ≤
      (SimpleGraph.binomialRandom (Fin N) ⟨p, le_of_lt hp.1, hp.2⟩).real
        {G | SimpleGraph.IsContained H
          (SimpleGraph.fromEdgeSet ((T.queriesOn G : Set (Sym2 (Fin N))) ∩ G.edgeSet))} ∧
      q = (T.queryCount : ℝ)}

/-- **Conjecture 16**. A `2`-degenerate graph which is not `(1,1)`-degenerate has query complexity
`f(H, p) = b ^ (2 - o(1))`, where `b = 1 / p` tends to infinity.

The asymptotic is stated as two-sided exponent bounds. -/
theorem conjecture_16_two_degenerate_query_exponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : IsDegenerate H 2) (hnot : ¬IsOneDegeneratePartition H)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ b : ℝ in Filter.atTop, 1 < b ∧
      ∀ hp : 0 < b⁻¹ ∧ b⁻¹ ≤ 1,
        b ^ (2 - ε) ≤ adaptiveSubgraphQueryCost H b⁻¹ hp ∧
        adaptiveSubgraphQueryCost H b⁻¹ hp ≤ b ^ (2 + ε) := by
  sorry

end Alweiss2021Subgraph
