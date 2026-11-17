import Mathlib

/-!
# Graphs With the Same Edge Count in Each Neighborhood

Authors: Nathan S. Sheffield and Zoe Xi.
Origin: [University of Minnesota Duluth REU 2024](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: N. S. Sheffield and Z. Xi, *Graphs With the Same Edge Count in Each Neighborhood*,
arXiv:2507.14473.
-/

namespace Sheffield2025Graphs

open scoped Classical in
/-- Every vertex has degree `r` and its open neighborhood induces `c` edges (Section 1). -/
def IsTriangleRegular {V : Type*} [Fintype V] (G : SimpleGraph V) (r c : ℕ) : Prop :=
  G.IsRegularOfDegree r ∧ ∀ v, (G.induce (G.neighborSet v)).edgeSet.ncard = c

/-- **Conjecture 1**. Every pair realized by a finite nonempty triangle-regular graph is
realized by a finite abelian Cayley graph. -/
theorem conjecture_1 {V : Type*} [Fintype V] [Nonempty V]
    (r c : ℕ) (G : SimpleGraph V) (hG : IsTriangleRegular G r c) :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Fintype A) (S : Set A),
      0 ∉ S ∧ (∀ a, a ∈ S ↔ -a ∈ S) ∧
        IsTriangleRegular (SimpleGraph.addCayley S) r c := by
  sorry

end Sheffield2025Graphs
