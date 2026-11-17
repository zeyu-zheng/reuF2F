import Mathlib

/-!
# Leading Digits of Mersenne Numbers

Authors: Zhaodong Cai, Matthew Faust, A. J. Hildebrand, Junxian Li, and Yuan Zhang.
Origin: [Illinois Geometry Lab
2016](https://iml.math.illinois.edu/research/publications-products-from-igl-research-groups/).
Reference: Z. Cai, M. Faust, A. J. Hildebrand, J. Li, and Y. Zhang, *Leading digits of Mersenne
numbers*, preprint; arXiv:1712.04425v3 (2018; first version 2017).
-/

namespace Cai2021Leading

open scoped Topology
open Finset

/-- The base-ten leading digit `D` of a positive natural number ((2.1)). The junk value at zero
is zero. -/
def leadingDigit (m : ℕ) : ℕ :=
  m / 10 ^ Nat.log 10 m

/-- **Conjecture 2.7** (with Definition 2.2). Among consecutive Mersenne numbers, every
positive-length tuple of leading digits has limiting frequency equal to the product of the
Benford frequencies.

All starts `1 ≤ n ≤ N` count, including blocks extending beyond `N`, and
`Nat.nth Nat.Prime (n - 1)` represents `p_n`, with `p_1 = 2`. -/
theorem conjecture_2_7 {k : ℕ} (hk : 1 ≤ k) (digits : Fin k → ℕ)
    (hdigits : ∀ i, 1 ≤ digits i ∧ digits i ≤ 9) :
    Filter.Tendsto
      (fun N : ℕ ↦
        (#{n ∈ Finset.Icc 1 N | ∀ i : Fin k,
            leadingDigit (mersenne (Nat.nth Nat.Prime (n + i.val - 1))) = digits i} :
          ℝ) / (N : ℝ))
      Filter.atTop
      (𝓝 (∏ i : Fin k, Real.logb 10 (1 + 1 / (digits i : ℝ)))) := by sorry

end Cai2021Leading
