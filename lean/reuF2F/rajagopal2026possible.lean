import Mathlib

/-!
# Possible Sizes of Sumsets

Author: Isaac Rajagopal.
Origin: [University of Minnesota Duluth REU
2025](https://sites.google.com/view/gallian-reu/additional-information/program-bibliography).
Reference: I. Rajagopal, *Possible sizes of sumsets*, Discrete Anal. (2026), Paper No. 2, 24 pp.;
doi:10.19086/da.165102.
-/

noncomputable section

namespace Rajagopal2026Possible

open scoped Pointwise
open Finset

/-- The range `R(h,k)` of cardinalities of `h`-fold sumsets of `k`-element integer sets
(Definition 1.1). -/
def sumsetSizeRange (h k : ℕ) : Set ℕ :=
  {n | ∃ A : Finset ℤ, #A = k ∧ #(h • A) = n}

/-- The forbidden triangular set `Delta_{h,k}` (Definition 1.2). -/
def forbiddenDelta (h k : ℕ) : Set ℕ :=
  {n | ∃ l : ℕ,
    l < Nat.min h k - 2 ∧
      h * k - h + 1 + l * h + 1 ≤ n ∧
        n ≤ h * k - h + 1 + l * h + (h - 2 - l)}

/-- **Conjecture 1.6**. For `k > h`, the range `R(h,k)` is exactly the standard interval with
the triangular forbidden set `Delta_{h,k}` removed. -/
theorem conjecture_1_6_predicted_range (h k : ℕ) (hh : 0 < h) (hk : h < k) :
    sumsetSizeRange h k =
      Set.Icc (h * k - h + 1) (Nat.choose (h + k - 1) h) \ forbiddenDelta h k := by
  sorry

end Rajagopal2026Possible
