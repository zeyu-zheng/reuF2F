import Mathlib

/-!
# Unimodality and monotonic portions of certain domination polynomials

Authors: Amanda Burcroff and Grace O'Brien.
Origin: [University of Minnesota Duluth REU 2021](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: A. Burcroff and G. O'Brien, *Unimodality and monotonic portions of certain domination
polynomials*, Discrete Math. **346** (2023), no. 9, 113508.
-/

namespace Burcroff2023Unimodality

open Finset

/-- The spider with one central vertex and disjoint legs of the given lengths, each counting the
vertices outside the center (Section 2). -/
def spider {t : ℕ} (lengths : Fin t → ℕ) :
    SimpleGraph (Option ((i : Fin t) × Fin (lengths i))) :=
  SimpleGraph.fromRel fun u v ↦
    match u, v with
    | none, some b => b.2.val = 0
    | some a, some b =>
        ∃ h : a.1 = b.1,
          (SimpleGraph.pathGraph (lengths b.1)).Adj (h ▸ a.2) b.2
    | _, _ => False

open scoped Classical in
/-- The domination polynomial, counting dominating vertex sets by cardinality (Section 1). -/
noncomputable def dominationPolynomial {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Polynomial ℕ :=
  ∑ s ∈ (Finset.univ : Finset V).powerset with ∀ v, v ∈ s ∨ ∃ w ∈ s, G.Adj v w,
    Polynomial.X ^ #s

/-- **Conjecture 3.7**. A spider with legs of length at most three and any leaf-deleted spider
have unimodal domination polynomials with some pair of modes at distance at most one. -/
theorem conjecture_3_7 {t : ℕ} (lengths : Fin t → ℕ)
    (hlengths : ∀ i, 1 ≤ lengths i ∧ lengths i ≤ 3)
    (v : Option ((i : Fin t) × Fin (lengths i)))
    (hleaf : ((spider lengths).neighborSet v).ncard = 1) :
    let q := dominationPolynomial ((spider lengths).induce {w | w ≠ v})
    ∃ μ ν : ℕ,
      MonotoneOn (dominationPolynomial (spider lengths)).coeff (Set.Iic μ) ∧
      AntitoneOn (dominationPolynomial (spider lengths)).coeff (Set.Ici μ) ∧
      MonotoneOn q.coeff (Set.Iic ν) ∧ AntitoneOn q.coeff (Set.Ici ν) ∧
      Nat.dist μ ν ≤ 1 := by
  sorry

end Burcroff2023Unimodality
