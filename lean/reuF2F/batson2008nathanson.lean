import Mathlib

/-!
# Nathanson heights in finite vector spaces

Author: Joshua Batson.
Origin: [University of Minnesota Duluth REU 2007](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: J. Batson, *Nathanson heights in finite vector spaces*, J. Number Theory **128** (2008),
no. 9, 2616-2633.
-/

noncomputable section

namespace Batson2008Nathanson

open scoped Topology

/-- The Nathanson height: the least sum of nonnegative coordinate representatives of a nonzero
vector in the subspace (Section 1). -/
def nathansonHeight {p n : ℕ} (V : Submodule (ZMod p) (Fin n → ZMod p)) : ℕ :=
  sInf {k | ∃ v ∈ V, v ≠ 0 ∧ ∑ i, (v i).val = k}

/-- The limiting height of an integer vector (Section 5). It takes the punctured liminf of the
sum of fractional parts, then the infimum over one period. -/
def limitingHeight {n : ℕ} (a : Fin n → ℤ) : ℝ :=
  sInf ((fun x : ℝ ↦
    Filter.liminf (fun t : ℝ ↦ ∑ i, Int.fract ((a i : ℝ) * t)) (𝓝[≠] x)) ''
      Set.Ico (0 : ℝ) 1)

/-- **Unnumbered conjecture** (Section 7, p. 16). For every fixed codimension, the normalized
Nathanson-height range approaches the limiting-height range at rate `O(p ^ (-1 / n))`. -/
theorem conjecture_section_7 (n m : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
    (fun p : Nat.Primes ↦
      Metric.hausdorffDist
        {x : ℝ | ∃ a ≠ (0 : Fin (m + 1) → ℤ), limitingHeight a = x}
        {x : ℝ | ∃ V : Submodule (ZMod (p : ℕ)) (Fin n → ZMod (p : ℕ)),
          Module.finrank (ZMod (p : ℕ)) V = n - m ∧
            (nathansonHeight V : ℝ) / (p : ℕ) = x})
      =O[Filter.comap (fun p : Nat.Primes ↦ (p : ℕ)) Filter.atTop]
        (fun p : Nat.Primes ↦ ((p : ℕ) : ℝ) ^ (-(1 : ℝ) / n)) := by
  sorry

end Batson2008Nathanson
