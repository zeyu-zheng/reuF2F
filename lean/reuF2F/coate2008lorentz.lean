import Mathlib

/-!
# The Lorentz Lattice Gas Model

Author: Benjamin Coate.
Origin: [Oregon State University REU
2008](https://sites.science.oregonstate.edu/math_reu/proceedings/2008.html).
Reference: B. Coate, *The Lorentz Lattice Gas Model*, Oregon State University Research
Experiences for Undergraduates Proceedings (2008), 37--48.
-/

noncomputable section

namespace Coate2008Lorentz

open MeasureTheory Filter
open scoped Topology

/-- The position and outgoing velocity of the northward light ray (Sections 1--2). One uniform
coordinate per vertex fixes its mirror for all visits (below `p / 2` NW, then NE up to `p`,
else vacant), and the origin's mirror acts only on later arrivals. -/
def ray (p : ℝ) (u : ℤ × ℤ → unitInterval) :
    ℕ → (ℤ × ℤ) × (ℤ × ℤ)
  | 0 => ((0, 0), (0, 1))
  | t + 1 =>
      let s := ray p u t
      let x : ℤ × ℤ := (s.1.1 + s.2.1, s.1.2 + s.2.2)
      let v : ℤ × ℤ :=
        if (u x : ℝ) < p / 2 then (-s.2.2, -s.2.1)
        else if (u x : ℝ) < p then (s.2.2, s.2.1)
        else s.2
      (x, v)

/-- **Conjecture 4.2** (p. 47). Above every density lower bound in `(0, 1)` there is a nonempty
open interval on which the probability of reaching the boundary of a growing centered odd
square tends to zero.

Radius `r` means side length `2 * r + 1`; the event is boundary hitting at any time, not
finite-time escape or return to the origin. The domain of `α` follows pp. 42--43. -/
theorem recurrence_intervals (α : ℝ) (hpos : 0 < α) (hlt : α < 1) :
    ∃ p₁ p₂ : ℝ, α ≤ p₁ ∧ p₁ < p₂ ∧ p₂ ≤ 1 ∧
      ∀ p : ℝ, p₁ < p → p < p₂ →
        Tendsto (fun r : ℕ ↦
          (Measure.infinitePi (fun _ : ℤ × ℤ ↦ (volume : Measure unitInterval)))
            {u | ∃ t : ℕ, max (ray p u t).1.1.natAbs (ray p u t).1.2.natAbs = r}) atTop (𝓝 0) := by
  sorry

end Coate2008Lorentz
