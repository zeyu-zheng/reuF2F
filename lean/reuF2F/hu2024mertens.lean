import Mathlib

/-!
# On a Mertens-type conjecture for number fields

Authors: Daniel Hu, Ikuya Kaneko, Spencer Martin, and Carl Schildkraut.
Origin: [University of Virginia REU 2021](https://uva.theopenscholar.com/ken-ono/reus-archive-2021).
Reference: D. Hu, I. Kaneko, S. Martin, and C. Schildkraut, *On a Mertens-type conjecture for
number fields*, Math. Proc. Cambridge Philos. Soc. **177** (2024), 481–523;
doi:10.1017/S0305004124000306.
-/

noncomputable section

namespace Hu2024Mertens

open scoped NumberField

open scoped Classical in
/-- The Mertens function of `K`, with half weight at norm exactly `x` (Section 1, p. 482). -/
def mertens (K : Type*) [Field K] [NumberField K] (x : ℝ) : ℝ :=
  ∑ I ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊x⌋₊).toFinset.erase ⊥,
    if (Ideal.absNorm I : ℝ) = x then (UniqueFactorizationMonoid.moebius I : ℝ) / 2
    else (UniqueFactorizationMonoid.moebius I : ℝ)

/-- **Conjecture 6.1** (p. 517). Infinitely many number fields, up to isomorphism, have only
finitely many Mertens sign changes.

Since the half-weighted function is constant between consecutive integers, finitely many sign
changes means eventual nonnegativity or nonpositivity, allowing zeros. No dicyclic or analytic
hypothesis is imposed. -/
theorem conjecture_6_1 :
    ∃ (K : ℕ → Type) (fields : ∀ n, Field (K n)),
      letI := fields
      ∃ (numberFields : ∀ n, NumberField (K n)),
        letI := numberFields
        (∀ i j, i ≠ j → IsEmpty (K i ≃+* K j)) ∧
        ∀ n, ∃ X ≥ (1 : ℝ),
          ((∀ x ≥ X, 0 ≤ mertens (K n) x) ∨
           (∀ x ≥ X, mertens (K n) x ≤ 0)) := by
  sorry

end Hu2024Mertens
