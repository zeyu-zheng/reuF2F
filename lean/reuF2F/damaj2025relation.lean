import Mathlib

/-!
# A relation on (omega, <) of intermediate degree spectrum on a cone

Authors: Jad Damaj and Matthew Harrison-Trainor.
Origin: [University of Michigan REU
2023](https://lsa.umich.edu/content/dam/math-assets/reu-su22/reu-2023/Damaj%2CJad_REU_Report_2023.pdf).
Reference: J. Damaj and M. Harrison-Trainor, *A relation on (omega, <) of intermediate degree
spectrum on a cone*, J. Symbolic Logic (2025), 1--39; doi:10.1017/jsl.2025.10164.
-/

namespace Damaj2025Relation

/-- Every point lies in a finite interval closed under the function and under all inverse images
(Definition 2.6). The function need not be injective. -/
def IsBlockFunction (f : ℕ → ℕ) : Prop :=
  ∀ n, ∃ a b : ℕ,
    n ∈ Set.Icc a b ∧ ∀ x, (f x ∈ Set.Icc a b ↔ x ∈ Set.Icc a b)

/-- The degree spectrum on `(ω, <)`: the degrees of transported functions joined with `X`
(Definition 2.3). -/
def relativeDegreeSpectrum (f : ℕ → ℕ) (X : ℕ → Bool) : Set TuringDegree :=
  fun d ↦ ∃ e : Equiv.Perm ℕ,
    ComputableIn {fun n ↦ Part.some (X n).toNat}
        (fun p : ℕ × ℕ ↦ decide (e.symm p.1 < e.symm p.2)) ∧
      d = toAntisymmetrization TuringReducible
        (fun n ↦ Part.some
          (if n % 2 = 0 then e (f (e.symm (n / 2))) else (X (n / 2)).toNat))

/-- **Conjecture 4.16**. Two block functions have incomparable degree spectra on a cone.

Containment on a cone is interpreted as eventual inclusion, as in Definition 2.4. -/
theorem conjecture_4_16 :
    ∃ f g : ℕ → ℕ,
      IsBlockFunction f ∧ IsBlockFunction g ∧
        (¬∃ X : ℕ → Bool,
          ∀ Y : ℕ → Bool,
            TuringReducible (fun n ↦ Part.some (X n).toNat)
              (fun n ↦ Part.some (Y n).toNat) →
            relativeDegreeSpectrum f Y ⊆ relativeDegreeSpectrum g Y) ∧
        ¬∃ X : ℕ → Bool,
          ∀ Y : ℕ → Bool,
            TuringReducible (fun n ↦ Part.some (X n).toNat)
              (fun n ↦ Part.some (Y n).toNat) →
            relativeDegreeSpectrum g Y ⊆ relativeDegreeSpectrum f Y := by
  sorry

end Damaj2025Relation
