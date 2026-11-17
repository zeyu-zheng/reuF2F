import Mathlib

/-!
# On Gaps in the Closures of Images of Divisor Functions

Authors: Niven Achenjang and Aaron Berger.
Origin: [University of Minnesota Duluth REU 2018](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: N. Achenjang and A. Berger, *On gaps in the closures of images of divisor functions*,
Int. J. Number Theory **15** (2019), no. 5, 1023-1036.
-/

namespace Achenjang2019Gaps

/-- **Conjecture 7.2** (Divisor Function Monotonicity). The number of connected
components of the closure of the negative-power divisor-sum range is nondecreasing
as the real parameter `r > 1` increases. -/
theorem conjecture_7_2 :
    let σ : ℝ → ℕ+ → ℝ := fun r n ↦
      ∑ d ∈ (n : ℕ).divisors, (d : ℝ) ^ (-r)
    MonotoneOn
      (fun r : ℝ ↦ Nat.card (ConnectedComponents (closure (Set.range (σ r)))))
      (Set.Ioi 1) := by
  sorry

end Achenjang2019Gaps
