import Mathlib

/-!
# Modeling Random Walks to Infinity on Primes in Z[sqrt(2)]

Authors: Bencheng Li, Steven J. Miller, Tudor Popescu, Daniel Sarnecki, and
Nawapan Wattanawanichkul.
Origin: [Polymath Jr. 2020](https://ploynawapan.github.io/talks/2020-09-01-talk-4).
Reference: B. Li, S. J. Miller, T. Popescu, D. Sarnecki, and N. Wattanawanichkul, *Modeling
random walks to infinity on primes in Z[sqrt(2)]*, J. Integer Seq. **25** (2022),
Article 22.6.1, 21 pp.
-/

namespace Li2022Modeling

/-- **Conjecture 22** (preprint Conjecture 4.1). No bounded-step walk on primes of `ℤ[√2]` has
unbounded range in the Euclidean coefficient plane `(a, b)`.

Primes are the irreducible elements of this UFD; no fixed start, quadrant, increasing-radius or
bounded-strip restriction is imposed. -/
theorem conjecture_22 (k : ℕ) (hk : 0 < k) :
    let point : Zsqrtd 2 → EuclideanSpace ℝ (Fin 2) :=
      fun z ↦ WithLp.toLp 2 ![(z.re : ℝ), (z.im : ℝ)]
    ¬∃ w : ℕ → Zsqrtd 2,
      (∀ n, Irreducible (w n)) ∧
      (∀ n, dist (point (w n)) (point (w (n + 1))) ≤ (k : ℝ)) ∧
      ¬Bornology.IsBounded (Set.range (fun n ↦ point (w n))) := by
  sorry

end Li2022Modeling
