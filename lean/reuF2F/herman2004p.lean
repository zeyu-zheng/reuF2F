import Mathlib

/-!
# p-Energy and p-Harmonic Functions on Sierpinski Gasket Type Fractals

Authors: P. Edward Herman, Roberto Peirone, and Robert S. Strichartz.
Origin: [Cornell Mathematics REU](https://math.cornell.edu/history-reu-and-spur-programs-department-mathematics).
Reference: P. E. Herman, R. Peirone, and R. S. Strichartz, *p-Energy and p-Harmonic Functions on
Sierpinski Gasket Type Fractals*, Potential Analysis **20** (2004), 125–148.
-/

noncomputable section

namespace Herman2004P

/-- The boundary energy reconstructed by (2.10), including the constant triple and even extension.
`projIcc` only supplies the subtype for a ratio already in `[0,1]`. -/
def boundaryEnergy (p : ℝ) (g : unitInterval → ℝ)
    (a : Fin 3 → ℝ) : ℝ :=
  let lo := min (a 0) (min (a 1) (a 2))
  let hi := max (a 0) (max (a 1) (a 2))
  let mid := a 0 + a 1 + a 2 - lo - hi
  if lo = hi then 0 else
    ((hi - lo) / 2) ^ p *
      g (Set.projIcc 0 1 zero_le_one (|2 * mid - lo - hi| / (hi - lo)))

/-- Positive continuous normalized profiles whose reconstructed three-variable energy is convex
(Definition 3.1), without the `G_0` restriction. -/
def G (p : ℝ) : Set (unitInterval → ℝ) :=
  {g | Continuous g ∧ (∀ x, 0 < g x) ∧ g 1 = 1 ∧
    ConvexOn ℝ Set.univ (boundaryEnergy p g)}

/-- The trace minimum value over all three real interior vertex values (following (2.14)). It is
an infimum, attained for `p > 1` and `g ∈ G`. -/
def traceEnergy (p : ℝ) (g : unitInterval → ℝ)
    (a : Fin 3 → ℝ) : ℝ :=
  sInf (Set.range (fun b : Fin 3 → ℝ ↦
    boundaryEnergy p g ![a 0, b 1, b 2] +
    boundaryEnergy p g ![b 0, a 1, b 2] +
    boundaryEnergy p g ![b 0, b 1, a 2]))

/-- The three-cell trace followed by normalization at `1` (Equations (3.1)–(3.2)). Values outside
`G` are unused junk. -/
def normalizedT (p : ℝ) (g : unitInterval → ℝ) : unitInterval → ℝ :=
  fun x ↦ traceEnergy p g ![-1, (x : ℝ), 1] /
    traceEnergy p g ![-1, 1, 1]

/-- **Unnumbered conjecture** (Introduction, p. 129). For `p > 1`, the normalized operator has a
unique fixed point in `G`, and every start in `G` converges to it uniformly on `[0,1]`.

Global attraction is read from the cited Peirone context rather than from expanded quantifiers in
the source. -/
theorem unique_fixed_point_global_attraction (p : ℝ) (hp : 1 < p) :
    ∃ gp ∈ G p, normalizedT p gp = gp ∧
      (∀ g ∈ G p, normalizedT p g = g → g = gp) ∧
      (∀ g ∈ G p,
        TendstoUniformly (fun n : ℕ ↦ (normalizedT p)^[n] g) gp Filter.atTop) := by
  sorry

end Herman2004P
