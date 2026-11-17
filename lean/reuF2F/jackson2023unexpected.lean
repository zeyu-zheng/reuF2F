import Mathlib

/-!
# Unexpected biases between congruence classes for parts in k-indivisible partitions

Authors: Faye Jackson and Misheel Otgonbayar.
Origin: [University of Virginia REU 2022](https://uva.theopenscholar.com/ken-ono/reus-archive-2022).
Reference: F. Jackson and M. Otgonbayar, *Unexpected biases between congruence classes for parts
in k-indivisible partitions*, J. Number Theory **248** (2023), 310–342.
-/

noncomputable section

namespace Jackson2023Unexpected

/-- The total number of occurrences of parts congruent to `r` modulo `t` among partitions of `n`
with no part divisible by `k` (Equation (1.4)). -/
def residuePartCount (k r t n : ℕ) : ℕ :=
  ∑ lam ∈ Nat.Partition.restricted n (fun m ↦ m % k ≠ 0),
    (lam.parts.filter (fun m ↦ m % t = r % t)).card

/-- The `k`-indivisible strict bias ordering (Section 1). Index `i` represents the residue
representative `i + 1` in `{1, …, t}`. -/
def BiasOrder (k t : ℕ) (r s : Fin t) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop,
    residuePartCount k (r.val + 1) t n < residuePartCount k (s.val + 1) t n

/-- The number `O(t)` of distinct bias orderings as `k ≥ 2` ranges over integers coprime to `t`
(Section 1). -/
def orderingCount (t : ℕ) : ℕ :=
  Nat.card { R : Fin t → Fin t → Prop //
    ∃ k ≥ 2, Nat.Coprime k t ∧ R = BiasOrder k t }

/-- **Conjecture 1.5**. The ratio `O(t) / φ(t)` grows sublinearly and superlogarithmically as `t`
tends to infinity.

Both bounds are retained; the separate no-ties conjecture is not included. -/
theorem conjecture_1_5 :
    let q : ℕ → ℝ := fun t ↦ (orderingCount t : ℝ) / (Nat.totient t : ℝ)
    Asymptotics.IsLittleO Filter.atTop q (fun t : ℕ ↦ (t : ℝ)) ∧
      Asymptotics.IsLittleO Filter.atTop (fun t : ℕ ↦ Real.log (t : ℝ)) q := by
  sorry

end Jackson2023Unexpected
