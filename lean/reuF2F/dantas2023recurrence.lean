import Mathlib

/-!
# Recurrence Relations for S-Legal Index Difference Sequences

Authors: Guilherme Zeus Dantas e Moura, Andrew Keisling, Astrid Lilly, Annika Mauro,
Steven J. Miller, Matthew Phang, and Santiago Velazquez Iannuzzelli.
Origin: [Williams College SMALL REU
2022](https://web.williams.edu/Mathematics/sjmiller/public_html/math/talks/SLIDs_FibConf2022.pdf).
Reference: G. Z. Dantas e Moura, A. Keisling, A. Lilly, A. Mauro, S. J. Miller, M. Phang, and
S. Velazquez Iannuzzelli, *Recurrence relations for S-legal index difference sequences*,
Fibonacci Quart. **61** (2023), no. 3, 257--274.
-/

namespace Dantas2023Recurrence

/-- The sequence whose terms are the least positive integers not represented by an `S`-legal sum
of earlier terms (Definition 1.9). The unused zeroth term is zero, and summands are restricted
to source indices `1, ..., n - 1`. -/
noncomputable def sLIDSequence (S : Finset ℕ) : ℕ → ℕ :=
  Nat.strongRec fun n previous ↦
    if n = 0 then 0 else
      sInf {m : ℕ | 0 < m ∧
        ∀ L : Finset (Fin n),
          (∀ i ∈ L, 0 < i.val) →
          (∀ i ∈ L, ∀ j ∈ L, Nat.dist i.val j.val ∉ S) →
          (∑ i ∈ L, previous i.val i.isLt) ≠ m}

/-- **Conjecture 2.8**. Deleting the difference `k - 1` from `{1, ..., k}` gives the recurrence
`a_(n+1) = a_n + a_(n-k)` for every `k ≥ 2` and `n > k + 1`. -/
theorem conjecture_2_8 (k n : ℕ) (hk : 2 ≤ k) (hn : k + 1 < n) :
    sLIDSequence ((Finset.Icc 1 k).erase (k - 1)) (n + 1) =
      sLIDSequence ((Finset.Icc 1 k).erase (k - 1)) n +
        sLIDSequence ((Finset.Icc 1 k).erase (k - 1)) (n - k) := by
  sorry

end Dantas2023Recurrence
