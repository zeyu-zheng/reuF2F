import Mathlib

/-!
# Growth functions of finitely generated algebras

Authors: Eric Fredette, Dan Kubala, Eric Nelson, Kelsey Wells, and Harold W. Ellingsen, Jr.
Origin: [SUNY Potsdam-Clarkson REU 2012](https://people.clarkson.edu/~ctamon/reu/reu-papers.html).
Reference: E. Fredette, D. Kubala, E. Nelson, K. Wells, and H. W. Ellingsen, Jr., *Growth
functions of finitely generated algebras*, Involve **8** (2015), 71-74;
doi:10.2140/involve.2015.8.71.
-/

noncomputable section

namespace Fredette2015Growth

open Finset

open scoped Classical in
/-- The number of normal words of length at most `n` (p. 71). Letters `false` and `true` are
the two free generators, and by the p. 71 basis convention this is the growth function of the
monomial quotient. -/
def growthFunction (relations : Finset (List Bool)) (n : ℕ) : ℕ :=
  #{w ∈ (List.finite_length_le Bool n).toFinset | ∀ r ∈ relations, ¬r <:+: w}

/-- **Final conjecture** (p. 74). The upper bound for polynomial growth degree is attained for
every maximal defining-word length `d + 1` with `d ≥ 2`.

Polynomial growth degree means asymptotic order, not equality to one polynomial at every
argument. -/
theorem sharp_growth_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ relations : Finset (List Bool),
      (∀ r ∈ relations, r.length ≤ d + 1) ∧
      (∃ r ∈ relations, r.length = d + 1) ∧
      Asymptotics.IsTheta Filter.atTop
        (fun n : ℕ ↦ (growthFunction relations n : ℝ))
        (fun n : ℕ ↦ (n : ℝ) ^
          ((∑ k ∈ d.divisors, Nat.totient k * 2 ^ (d / k)) / d)) := by
  sorry

end Fredette2015Growth
