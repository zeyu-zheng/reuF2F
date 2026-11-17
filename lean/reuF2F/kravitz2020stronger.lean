import Mathlib

/-!
# A stronger connection between the Erdős-Burgess and Davenport constants

Authors: Noah Kravitz and Ashwin Sah.
Origin: [University of Minnesota Duluth REU](https://www.mit.edu/~asah/papers/1808.06031.pdf).
Reference: N. Kravitz and A. Sah, *A stronger connection between the Erdős-Burgess and Davenport
constants*, J. Number Theory **210** (2020), 373-388; arXiv:1808.06031v1.
-/

namespace Kravitz2020Stronger

/-- **Question 6.1** (Section 6, p. 13), first part. In every longest sequence over `ℤ/nℤ`
with no nonempty subsequence whose product is idempotent, every element is squarefree with
respect to each prime divisor of `n` and coprime to each prime dividing `n` exactly once.

The classification part of the question is not formalized. The length `I(ℤ/nℤ) - 1` is encoded
as maximality among all such sequences, and the prime conditions are tested on the canonical
representative `a.val`. -/
theorem question_6_1 (n : ℕ) (hn : 1 < n) (S : List (ZMod n))
    (hfree : ¬∃ T : List (ZMod n), T.Sublist S ∧ T ≠ [] ∧ T.prod * T.prod = T.prod)
    (hgreatest : ∀ U : List (ZMod n),
      (¬∃ V : List (ZMod n), V.Sublist U ∧ V ≠ [] ∧ V.prod * V.prod = V.prod) →
        U.length ≤ S.length)
    (a : ZMod n) (ha : a ∈ S) (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) :
    ¬p ^ 2 ∣ a.val ∧ (¬p ^ 2 ∣ n → ¬p ∣ a.val) := by
  sorry

end Kravitz2020Stronger
