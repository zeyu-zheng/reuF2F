import Mathlib

/-!
# Generalizations of Alder's conjecture via Kang--Park

Authors: Adriana L. Duncan, Simran Khunger, Holly Swisher, and Ryan Tamura.
Origin: [Oregon State University REU
2020](https://sites.science.oregonstate.edu/math_reu/reucv.html).
Reference: A. L. Duncan, S. Khunger, H. Swisher, and R. Tamura, *Generalizations of Alder's
Conjecture via a Conjecture of Kang and Park*, arXiv:2010.08646.
-/

noncomputable section

namespace Duncan2020Generalizations

open Finset

/-- The count `q_d^{(a)}(n)` of partitions into parts at least `a` with successive parts differing
by at least `d` (Section 1). -/
def q (d a n : ℕ) : ℕ :=
  #{lam : Nat.Partition n | (∀ x ∈ lam.parts, a ≤ x) ∧
      (lam.parts.sort (· ≤ ·)).IsChain (fun x y : ℕ ↦ x + d ≤ y)}

/-- The count `Q_d^{(b,-,-)}(n)` of partitions into parts congruent to `±b` modulo `d + 3`,
excluding both `b` and `d + 3 - b` (before Conjecture 1.5). -/
def QminusMinus (d b n : ℕ) : ℕ :=
  #{lam : Nat.Partition n | ∀ x ∈ lam.parts,
      (x % (d + 3) = b % (d + 3) ∨ x % (d + 3) = (d + 3 - b) % (d + 3)) ∧
        x ≠ b ∧ x ≠ d + 3 - b}

/-- The signed difference `Delta_d^{(a,b,-,-)}(n)`. -/
def DeltaMinusMinus (d a b n : ℕ) : ℤ :=
  (q d a n : ℤ) - (QminusMinus d b n : ℤ)

/-- **Conjecture 1.5**. For positive `a, d` with `a ≤ d + 2`, all positive `n` satisfy
`Delta_d^{(a,a,-,-)}(n) ≥ 0`. -/
theorem conjecture_1_5_generalized_kang_park (a d n : ℕ)
    (ha : 1 ≤ a) (hd : 1 ≤ d) (had : a ≤ d + 2) (hn : 1 ≤ n) :
    0 ≤ DeltaMinusMinus d a a n := by sorry

end Duncan2020Generalizations
