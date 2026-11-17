import Mathlib

/-!
# Counting Shellings of Complete Bipartite Graphs and Trees

Author: Junyao Peng.
Origin: [MIT SPUR 2018](https://math.mit.edu/research/undergraduate/spur/past-projects.html).
Reference: J. Peng, *Counting shellings of complete bipartite graphs and trees*, MIT SPUR final
paper, August 1, 2018.
-/

namespace Peng2021Counting

/-- The number of edge orderings in which each edge after the first meets an earlier edge
(Definitions 1.2-1.3). -/
noncomputable def shellingNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  Nat.card {s : Fin (Nat.card G.edgeSet) ≃ G.edgeSet //
    ∀ i, 0 < i.val → ∃ j, j < i ∧ ∃ v ∈ (s i).val, v ∈ (s j).val}

/-- The complete tree, in which the root has `k` children and other nonleaves have `k - 1`
children (Conjecture 4.1, Figure 7). Vertices carry breadth-first labels. -/
def completeTree (k m : ℕ) :
    SimpleGraph (Fin ((k * (k - 1) ^ m - 2) / (k - 2))) :=
  SimpleGraph.fromRel fun a b ↦ b.val ≠ 0 ∧ a.val = (b.val - 2) / (k - 1)

/-- **Conjecture 4.1** (pp. 20-21). The complete depth-`m` tree maximizes the shelling number
among trees of the specified order and maximum degree at most `k`. -/
theorem conjecture_4_1 (k m : ℕ) (hk : 3 ≤ k) (hm : 0 < m)
    (T : SimpleGraph (Fin ((k * (k - 1) ^ m - 2) / (k - 2))))
    (hT : T.IsTree) (hdegree : ∀ v, (T.neighborSet v).ncard ≤ k) :
    shellingNumber T ≤ shellingNumber (completeTree k m) := by
  sorry

end Peng2021Counting
