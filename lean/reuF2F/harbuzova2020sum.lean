import Mathlib

/-!
# Sum-Product Estimates for Well-Spaced Sets

Author: Alina Harbuzova.
Origin: [MIT UROP+ 2020](https://math.mit.edu/research/undergraduate/urop-plus/papers.html).
Reference: A. Harbuzova, *Sum-Product Estimates for Well-Spaced Sets*, UROP+ Final Paper,
August 2020, 12 pp.;
https://math.mit.edu/research/undergraduate/urop-plus/documents/2020/Harbuzova.pdf.
-/

noncomputable section

namespace Harbuzova2020Sum

open scoped Pointwise
open Finset

open scoped Classical in
/-- The largest cardinality of a subset whose distinct points have distance at least `δ`
(Definitions 2.1 and 2.2). -/
def packingNumber (S : Finset ℝ) (δ : ℝ) : ℕ :=
  ({B ∈ S.powerset | (B : Set ℝ).Pairwise (fun x y ↦ δ ≤ |x - y|)} :
    Finset (Finset ℝ)).sup Finset.card

/-- **Conjecture 2** (Full-Size Conjecture, Section 3, p. 4). One exponent gives full-size sumset
or productset packing for every fixed positive spacing constant and positive exponent loss,
uniformly in the finite input set and its size.

The asymptotic notation is expanded with one `α` chosen before `c` and `ε`, and `K` independent of
`A` and its size; nonemptiness supplies the inverse-cardinality scale. -/
theorem conjecture_2 :
    ∃ α : ℝ, 1 < α ∧
      ∀ c > (0 : ℝ), ∀ ε > (0 : ℝ),
        ∃ K > (0 : ℝ),
          ∀ (A : Finset ℝ) (hA : A.Nonempty)
            (hinterval : (A : Set ℝ) ⊆ Set.Icc 1 2)
            (hspacing : (A : Set ℝ).Pairwise
              (fun a b ↦ c / (#A : ℝ) ≤ |a - b|)),
            K * ((#A : ℝ) ^ (-α)) ^ (-1 + ε) ≤
              max (packingNumber (A + A) ((#A : ℝ) ^ (-α)) : ℝ)
                (packingNumber (A * A) ((#A : ℝ) ^ (-α)) : ℝ) := by
  sorry

end Harbuzova2020Sum
