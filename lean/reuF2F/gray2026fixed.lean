import Mathlib

/-!
# Fixed perimeter analogues of some partition results

Authors: Gabriel Gray, Emily Payne, Holly Swisher, and Ren Watson.
Origin: [Oregon State University REU
2024](https://math.oregonstate.edu/sites/math.oregonstate.edu/files/2024-08/EmilyGabeRen_0.pdf).
Reference: G. Gray, E. Payne, H. Swisher, and R. Watson, *Fixed perimeter analogues of some
partition results*, preprint (2025), 15 pp.; arXiv:2502.12394v1.
-/

noncomputable section

namespace Gray2026Fixed

open Finset

/-- The largest hook length: largest part plus number of parts minus one. -/
def perimeter {s : ℕ} (p : Nat.Partition s) : ℕ :=
  p.parts.toFinset.sup id + p.parts.card - 1

open scoped Classical in
/-- The count `h_d^(a)(n)` of perimeter-`n` partitions with parts at least `a` and pairwise
differences at least `d` (Section 1.2). All partition sizes are included. -/
def distinctCount (a d n : ℕ) : ℕ :=
  ∑ s ∈ Finset.range (n * n + 1),
    #{p : Nat.Partition s |
      0 < p.parts.card ∧ perimeter p = n ∧
      (∀ x ∈ p.parts, a ≤ x) ∧
      p.parts.Pairwise (fun x y ↦ d ≤ Nat.dist x y)}

open scoped Classical in
/-- The count `ell_m^(m₁,m₂)(n)` of perimeter-`n` partitions whose positive parts lie in either
indicated residue class (Section 1.5). Zero residues are included. -/
def residueCount (m₁ m₂ m n : ℕ) : ℕ :=
  ∑ s ∈ Finset.range (n * n + 1),
    #{p : Nat.Partition s |
      0 < p.parts.card ∧ perimeter p = n ∧
      ∀ x ∈ p.parts, x % m = m₁ % m ∨ x % m = m₂ % m}

/-- **Conjecture 1.5**. The difference of the two fixed-perimeter counts diverges to positive or
negative infinity according as `m` is above or below `2d + 2`; no assertion is made at the
critical modulus. -/
theorem conjecture_1_5 (a d m₁ m₂ m : ℕ) (ha : 0 < a) (had : a ≤ d)
    (hm₁ : 0 < m₁) (hm₁₂ : m₁ < m₂) (hm₂ : m₂ ≤ m) :
    (2 * d + 2 < m → Filter.Tendsto
      (fun n : ℕ ↦ (distinctCount a d n : ℤ) - (residueCount m₁ m₂ m n : ℤ))
      Filter.atTop Filter.atTop) ∧
    (m < 2 * d + 2 → Filter.Tendsto
      (fun n : ℕ ↦ (distinctCount a d n : ℤ) - (residueCount m₁ m₂ m n : ℤ))
      Filter.atTop Filter.atBot) := by sorry

end Gray2026Fixed
