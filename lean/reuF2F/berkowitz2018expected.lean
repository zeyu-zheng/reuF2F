import Mathlib

/-!
# Expected Chromatic Number of Random Subgraphs

Authors: Ross Berkowitz, Pat Devlin, Catherine Lee, Henry Reichard, and David Townley.
Origin: [Yale SUMRY 2018](https://sumry.yale.edu/past-projects).
Reference: R. Berkowitz, P. Devlin, C. Lee, H. Reichard, and D. Townley, *Expected chromatic
number of random subgraphs*, preprint (2018), 14 pp.; arXiv:1811.02018v1.
-/

noncomputable section

namespace Berkowitz2018Expected

/-- **Conjecture 2**. Among finite simple graphs of chromatic number `n`, the complete graph on
`n` vertices minimizes the expected chromatic number after independent edge retention with
probability at most one half.

All vertices are retained, both probability endpoints are included, and no uniqueness is
asserted. -/
theorem conjecture_2 {V : Type*} [Finite V] (G : SimpleGraph V) (n : ℕ)
    (hn : G.chromaticNumber = n) (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2) :
    ∫ E : Set (Sym2 V), ((SimpleGraph.fromEdgeSet E).chromaticNumber.toNat : ℝ)
        ∂(ProbabilityTheory.setBernoulli G.edgeSet p) ≥
      ∫ E : Set (Sym2 (Fin n)), ((SimpleGraph.fromEdgeSet E).chromaticNumber.toNat : ℝ)
        ∂(ProbabilityTheory.setBernoulli
          (SimpleGraph.edgeSet (⊤ : SimpleGraph (Fin n))) p) := by
  sorry

end Berkowitz2018Expected
