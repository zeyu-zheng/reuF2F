import Mathlib

/-!
# Geodesics with Two Self-Intersections on the Punctured Torus

Authors: Susan Dziadosz, Thomas Insel, and Peter Wiles.
Origin: [Oregon State University REU
1994](https://sites.science.oregonstate.edu/math_reu/reucv.html).
Reference: S. Dziadosz, T. Insel, and P. Wiles, *Geodesics with Two Self-Intersections on the
Punctured Torus*, Oregon State University REU report (1994), 29--50.
-/

noncomputable section

namespace Dziadosz1994Geodesics

/-- The first generator of the modular commutator group (p. 29). -/
def A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, 1; 1, 2], by norm_num [Matrix.det_fin_two]⟩

/-- The second generator of the modular commutator group (p. 29). -/
def B : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, -1; -1, 2], by norm_num [Matrix.det_fin_two]⟩

/-- The fixed matrix realization, inverse to the marking `theta` after projection to the modular
group (p. 31). -/
def rho : FreeGroup (Fin 2) →* Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  FreeGroup.lift ![A, B]

/-- The real binary quadratic form `a * X ^ 2 + b * X * Y + c * Y ^ 2` of p. 48. -/
def binaryForm (a b c : ℝ) : QuadraticForm ℝ (Fin 2 → ℝ) :=
  a • QuadraticMap.proj 0 0 + b • QuadraticMap.proj 0 1 +
    c • QuadraticMap.proj 1 1

/-- The absolute infimum `m(f)` over all nonzero integer pairs (p. 48). -/
def markoffMinimum (f : QuadraticForm ℝ (Fin 2 → ℝ)) : ℝ :=
  sInf {v : ℝ | ∃ p q : ℤ,
    (p ≠ 0 ∨ q ≠ 0) ∧ v = |f ![(p : ℝ), (q : ℝ)]|}

/-- The normalized value `M(f)` with literal discriminant `b ^ 2 - 4 * a * c` (p. 48). It is
meaningful only for positive discriminant and infimum, as required in its use below. -/
def markoffValue (a b c : ℝ) : ℝ :=
  √(b ^ 2 - 4 * a * c) / markoffMinimum (binaryForm a b c)

/-- The finite real Markoff spectrum of all real indefinite forms (p. 48). Forms with zero
infimum are excluded by the positivity guard. -/
def markoffSpectrum : Set ℝ :=
  {v | ∃ a b c : ℝ, 0 < b ^ 2 - 4 * a * c ∧
    0 < markoffMinimum (binaryForm a b c) ∧ v = markoffValue a b c}

/-- **Conjecture 4.2** (p. 49). Every automorphic image of `a a b a b⁻¹` has its associated value
isolated in the Markoff spectrum.

The associated value is that of the form `t * X ^ 2 + (u - r) * X * Y - s * Y ^ 2` of the matrix
`[[r, s], [t, u]]` representing the image under the fixed marking, with no automorphism filtered;
the 1998 successor paper's limit-at-3 result is not isolation. -/
theorem conjecture_4_2 (g : MulAut (FreeGroup (Fin 2))) :
    let a := FreeGroup.of (0 : Fin 2)
    let b := FreeGroup.of (1 : Fin 2)
    let U := rho (g (a * a * b * a * b⁻¹))
    let v := markoffValue (U 1 0 : ℝ) ((U 1 1 : ℝ) - (U 0 0 : ℝ)) (-(U 0 1 : ℝ))
    v ∈ markoffSpectrum ∧
      ∃ ε > (0 : ℝ), ∀ w ∈ markoffSpectrum, |w - v| < ε → w = v := by
  sorry

end Dziadosz1994Geodesics
