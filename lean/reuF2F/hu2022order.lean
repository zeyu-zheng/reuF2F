import Mathlib

/-!
# Order of Zeros of Dedekind Zeta Functions

Authors: Daniel Hu, Ikuya Kaneko, Spencer Martin, and Carl Schildkraut.
Origin: [University of Virginia REU 2021](https://uva.theopenscholar.com/ken-ono/reus-archive-2021).
Reference: D. Hu, I. Kaneko, S. Martin, and C. Schildkraut, *Order of zeros of Dedekind zeta
functions*, Proc. Amer. Math. Soc. **150** (2022), 5111–5120; doi:10.1090/proc/16041;
arXiv:2107.03269v2.
-/

namespace Hu2022Order

/-- **Conjecture 6.2** (p. 8). For every irreducible complex representation of a relative Galois
group, the upper field's Dedekind zeta function has infinitely many distinct nontrivial zeros of
multiplicity at least the representation's degree.

The zeta function is specified by holomorphy off `1` and its convergent ideal series, which
identifies it with the continuation; its value at `1` is irrelevant. No Artin, GRH, monomiality
or absolute-Galois hypothesis is imposed. -/
theorem conjecture_6_2
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (L ≃ₐ[K] L) V) (hρ : ρ.IsIrreducible)
    (ζ : ℂ → ℂ) (hζ : DifferentiableOn ℂ ζ {s : ℂ | s ≠ 1})
    (hseries : ∀ s : ℂ, 1 < s.re → ζ s = NumberField.dedekindZeta L s) :
    Set.Infinite {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ ζ s = 0 ∧
      (Module.finrank ℂ V : ℕ∞) ≤ analyticOrderAt ζ s} := by
  sorry

end Hu2022Order
