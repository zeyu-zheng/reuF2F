import Mathlib

/-!
# Lattice Embeddings of Planar Point Sets

Authors: Michael Knopf, Jesse Milzman, Derek Smith, Dantong Zhu, and Dara Zirlin.
Origin: [Lafayette College REU 2014](https://math.lafayette.edu/opportunities/reu/publications/).
Reference: M. Knopf, J. Milzman, D. Smith, D. Zhu, and D. Zirlin, *Lattice Embeddings of Planar
Point Sets*, Discrete Comput. Geom. **56** (2016), 693-710; doi:10.1007/s00454-016-9812-4.
-/

noncomputable section

namespace Knopf2016Lattice

/-- The imaginary quadratic field, embedded in the complex plane (Section 2). -/
def quadraticField (D : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {Complex.I * (√(D : ℝ) : ℂ)}

/-- **Conjecture 1** (Section 5.1). Every integer-sided triangle of characteristic `D` embeds
congruently in the ring of integers of `ℚ(√-D)` if and only if every ideal in that ring has
principal square.

The characteristic is Section 3's `16 * area ^ 2 = D * m ^ 2` with `m > 0`, which excludes
degenerate triangles. -/
theorem conjecture_1 (D : ℕ) (hD : 0 < D) (hsq : Squarefree D) :
    (∀ u v w : ℂ,
      (∃ a : ℕ, dist u v = (a : ℝ)) →
      (∃ b : ℕ, dist v w = (b : ℝ)) →
      (∃ c : ℕ, dist w u = (c : ℝ)) →
      (∃ m > (0 : ℕ),
        4 * ((v - u).re * (w - u).im - (v - u).im * (w - u).re) ^ 2 =
          (D : ℝ) * (m : ℝ) ^ 2) →
      ∃ e : ℂ ≃ᵢ ℂ, ∀ z ∈ ({u, v, w} : Set ℂ),
        ∃ t : NumberField.RingOfIntegers (quadraticField D),
          e z = ((t : quadraticField D) : ℂ)) ↔
    ∀ I : Ideal (NumberField.RingOfIntegers (quadraticField D)),
      (I ^ 2).IsPrincipal := by
  sorry

end Knopf2016Lattice
