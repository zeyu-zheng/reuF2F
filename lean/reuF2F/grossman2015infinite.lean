import Mathlib

/-!
# An Infinite Family of Non-Abelian Monogenic Number Fields

Authors: Ofer Grossman and Dongkwan Kim.
Origin: [MIT SPUR 2015](https://math.mit.edu/research/undergraduate/spur/past-projects.html).
Reference: O. Grossman and D. Kim, *An Infinite Family of Non-Abelian Monogenic Number Fields*,
MIT research report, November 11, 2015, 8 pp.,
https://math.mit.edu/documents/spur/2015grossman-kim.pdf.
-/

namespace Grossman2015Infinite

/-- **Unnumbered conjecture** (Section 4, first paragraph, p. 7). For every `n ≥ 3`, there are
infinitely many pairwise non-isomorphic Galois number fields with Galois group `Sₙ` whose ring of
integers has a power integral basis.

The bound `n ≥ 3` expands the source's non-abelian antecedent. Each field is itself Galois, not
merely a degree-`n` field with `Sₙ` normal closure, so its power basis has length `n!`. -/
theorem symmetric_galois_monogenic_families (n : ℕ) (hn : 3 ≤ n) :
    ∃ (K : ℕ → Type) (fields : ∀ i, Field (K i)),
      letI := fields
      ∃ (numberFields : ∀ i, NumberField (K i)),
        letI := numberFields
        (∀ i j, i ≠ j → IsEmpty (K i ≃ₐ[ℚ] K j)) ∧
        ∀ i, IsGalois ℚ (K i) ∧
          Nonempty ((K i ≃ₐ[ℚ] K i) ≃* Equiv.Perm (Fin n)) ∧
          Nonempty (PowerBasis ℤ (NumberField.RingOfIntegers (K i))) := by
  sorry

end Grossman2015Infinite
