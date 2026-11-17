import Mathlib

/-!
# Almost Monochromatic Partitions of Two-Colored Planar Points Sets

Authors: Martin Balko and Martin Bohm.
Origin: [DIMACS-DIMATIA International REU 2012](https://iti.mff.cuni.cz/series/2012/569.pdf).
Reference: M. Balko and M. Bohm, *Almost monochromatic partitions of two-colored planar points
sets*, in J. Cibulka (ed.), DIMACS-DIMATIA International REU 2012, IUUK-ITI Series 2012-569,
8-15.
-/

noncomputable section

namespace Balko2012Almost

open Finset

/-- **Conjecture 1.9**. Every two-colored planar point set in general position has a
convex-hull-disjoint partition with at most `k` stains per part and at most `3 ⌈n / (6k + 5)⌉`
parts.

The source prints a question mark after the conjectured bound; the empty set is included
vacuously. -/
theorem conjecture_1_9 (k : ℕ)
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (color : EuclideanSpace ℝ (Fin 2) → Bool)
    (hgeneral : ∀ T : Finset (EuclideanSpace ℝ (Fin 2)),
      T ⊆ S → #T = 3 → AffineIndependent ℝ (fun x : T ↦ x.val)) :
    ∃ P : Finpartition S,
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B →
        Disjoint (convexHull ℝ (A : Set (EuclideanSpace ℝ (Fin 2))))
          (convexHull ℝ (B : Set (EuclideanSpace ℝ (Fin 2))))) ∧
      (∀ A ∈ P.parts,
        #{x ∈ A | color x = true} ≤ k ∨
        #{x ∈ A | color x = false} ≤ k) ∧
      #P.parts ≤ 3 * Nat.ceil ((#S : ℝ) / (6 * (k : ℝ) + 5)) := by
  sorry

end Balko2012Almost
