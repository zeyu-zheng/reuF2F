import Mathlib

/-!
# Lacunarity of Han-Nekrasov-Okounkov q-series

Authors: Katherine Gallagher, Lucia Li, and Katja Vassilev.
Origin: [Emory University REU in Number Theory
2018](https://uva.theopenscholar.com/ken-ono/reus-archive-2018).
Reference: K. Gallagher, L. Li, and K. Vassilev, *Lacunarity of Han-Nekrasov-Okounkov
q-series*, preprint (2018); arXiv:1807.04576v2.
-/

noncomputable section

open Filter
open scoped PowerSeries.WithPiTopology Topology

namespace Gallagher2020Lacunarity

open Finset

/-- The ordinary-`q` series of `F_{4,5,c}`, including its initial shift (equation (1.6)). -/
def hanSeries (c : PNat) : PowerSeries ℚ :=
  let e : PowerSeries ℚ :=
    tprod fun n : ℕ ↦ 1 - PowerSeries.X ^ (n + 1)
  PowerSeries.X ^ (4 * (c : ℕ) + 15) *
    (PowerSeries.expand 96 (by decide) e) ^ 4 *
    PowerSeries.expand (96 * (c : ℕ)) (Nat.mul_ne_zero (by decide) c.ne_zero) e *
    (PowerSeries.expand 24 (by decide) e)⁻¹

/-- **Unnumbered conjecture** (Section 4). All three exceptional series are lacunary: their zero
ordinary-`q` coefficients have natural density one. -/
theorem lacunarity (c : PNat) (hc : (c : ℕ) = 3 ∨ (c : ℕ) = 5 ∨ (c : ℕ) = 11) :
    Tendsto (fun N : ℕ ↦
      #{n ∈ Finset.range N | PowerSeries.coeff n (hanSeries c) = 0} /
        (N : ℝ)) atTop (𝓝 (1 : ℝ)) := by
  sorry

end Gallagher2020Lacunarity
