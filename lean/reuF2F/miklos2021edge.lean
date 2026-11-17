import Mathlib

/-!
# Edge disjoint caterpillar realizations

Authors: Istvan Miklos, Geneva Schlafly, Yuheng Wang, and Zhangyang Wei.
Origin: [Budapest Semesters in Mathematics](https://www.bsmath.hu/articles.html).
Reference: I. Miklos, G. Schlafly, Y. Wang, and Z. Wei, *Edge disjoint caterpillar
realizations*, Discrete Appl. Math. **289** (2021), 327-344; doi:10.1016/j.dam.2020.11.006.
-/

noncomputable section

namespace Miklos2021Edge

/-- A tree degree sequence: positive entries summing to `2n - 2` (Definition 1). -/
def IsTreeDegreeSequence {n : ℕ} (d : Fin n → ℕ) : Prop :=
  (∀ v, 0 < d v) ∧ (∑ v, d v) + 2 = 2 * n

open scoped Classical in
/-- A caterpillar: a tree whose non-leaf vertices induce a path (Definition 1). The two-vertex
tree has the empty backbone. -/
def IsCaterpillar {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  G.IsTree ∧
    ∃ m : ℕ, Nonempty ((G.induce {v | G.degree v ≠ 1}) ≃g SimpleGraph.pathGraph m)

open scoped Classical in
/-- **Conjecture 1**. Every tree degree matrix with each vertex a leaf in at most one row admits
pairwise edge-disjoint caterpillar realizations of all its rows.

The distinct-row condition follows the introduction and Section 6, where Definition 2 omits
the restriction on its row indices. -/
theorem conjecture_1 {k n : ℕ} (D : Matrix (Fin k) (Fin n) ℕ)
    (hD : ∀ i, IsTreeDegreeSequence (D i))
    (hleaves : ∀ i j, i ≠ j → ∀ v, D i v = 1 → D j v ≠ 1) :
    ∃ T : Fin k → SimpleGraph (Fin n),
      (∀ i, IsCaterpillar (T i)) ∧
      (∀ i v, (T i).degree v = D i v) ∧
      Pairwise (fun i j ↦ Disjoint (T i).edgeSet (T j).edgeSet) := by
  sorry

end Miklos2021Edge
