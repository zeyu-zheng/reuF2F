import Mathlib

/-!
# Biases among Congruence Classes for Parts in k-regular Partitions

Authors: Faye Jackson and Misheel Otgonbayar.
Origin: [University of Virginia REU
2022](https://math.uchicago.edu/~alephnil/papers/#biases-k-regular-partitions).
Reference: F. Jackson and M. Otgonbayar, *Biases among congruence classes for parts in k-regular
partitions*, arXiv:2207.04352 (2022), 25 pp.
-/

noncomputable section

namespace Jackson2022Biases

/-- The count `D_k(r,t;n)` of all occurrences of parts congruent to `r` modulo `t` among
partitions of `n` with every multiplicity below `k` (Section 1, p. 2). -/
def residuePartCount (k r t n : ℕ) : ℕ :=
  ∑ lam ∈ Nat.Partition.countRestricted n k,
    (lam.parts.filter (fun m ↦ m % t = r % t)).card

/-- **Conjecture 1.4**. For `t ≥ 6`, lower residue classes have weak bias for every `k ≥ 3` and
`n ≥ 1`, and strict bias for every `k ≥ 2` and `n > max(t + 3, 16)`.

Here `k`-regular means every multiplicity is below `k`, not indivisibility by `k`; neither clause
assumes coprimality. -/
theorem conjecture_1_4 (t r s : ℕ) (ht : 6 ≤ t) (hr : 1 ≤ r)
    (hrs : r < s) (hs : s ≤ t) :
    (∀ (k n : ℕ), 3 ≤ k → 1 ≤ n →
      residuePartCount k s t n ≤ residuePartCount k r t n) ∧
    (∀ (k n : ℕ), 2 ≤ k → max (t + 3) 16 < n →
      residuePartCount k s t n < residuePartCount k r t n) := by
  sorry

end Jackson2022Biases
