import Mathlib

/-!
# Non-Archimedean Henon Maps, Attractors, and Horseshoes

Authors: Kenneth Allen, David DeMark, and Clayton Petsche.
Origin: [Oregon State University REU
2016](https://sites.science.oregonstate.edu/math_reu/reucv.html).
Reference: K. Allen, D. DeMark, and C. Petsche, *Non-Archimedean Henon maps, attractors, and
horseshoes*, Res. Number Theory **4** (2018), Paper 5; doi:10.1007/s40993-018-0105-2.
-/

namespace Allen2018Non

/-- The quadratic Henon automorphism and its inverse (equations (1) and (2)). -/
def henon {K : Type*} [Field K] (a b : K) (hb : b ≠ 0) : Equiv.Perm (K × K) where
  toFun z := (a + b * z.2 - z.1 ^ 2, z.1)
  invFun z := (z.2, (-a + z.1 + z.2 ^ 2) / b)
  left_inv := by
    rintro ⟨x, y⟩
    apply Prod.ext
    · rfl
    · change (-a + (a + b * y - x ^ 2) + x ^ 2) / b = y
      field_simp [hb]
      ring
  right_inv := by
    rintro ⟨x, y⟩
    apply Prod.ext
    · change a + b * ((-a + x + y ^ 2) / b) - y ^ 2 = x
      field_simp [hb]
      ring
    · rfl

/-- The filled Julia set: points with bounded forward and backward orbits (equation (3)). The
product norm is the maximum of the two coordinate norms, as in the source. -/
def filledJulia {K : Type*} [NormedField K] (a b : K) (hb : b ≠ 0) : Set (K × K) :=
  {z | (∃ R : ℝ, ∀ n : ℕ,
      ‖((henon a b hb : K × K → K × K)^[n]) z‖ ≤ R) ∧
    (∃ R : ℝ, ∀ n : ℕ,
      ‖(((henon a b hb).symm : K × K → K × K)^[n]) z‖ ≤ R)}

/-- **Conjecture 1** (Section 4.2). Every complete, locally compact non-Archimedean field of odd
residue characteristic admits a quadratic Henon map in region `H_II^+` with infinite two-sided
filled Julia set.

Odd residue characteristic is expressed as `‖(2 : K)‖ = 1`, as in Section 2. -/
theorem conjecture_1 (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    [LocallyCompactSpace K] [IsUltrametricDist K] (hodd : ‖(2 : K)‖ = 1) :
    ∃ (a b : K) (hb : b ≠ 0),
      ‖a‖ ≤ 1 ∧ ‖b‖ < 1 ∧ (filledJulia a b hb).Infinite := by
  sorry

end Allen2018Non
