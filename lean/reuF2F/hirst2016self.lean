import Mathlib

/-!
# Self-Similarity in Level Set Trees of Geometric Random Walks

Authors: Anna-Sophia Hirst, Rachel Linder, and Daniel Malmuth.
Origin: [Oregon State University REU
2016](https://math.oregonstate.edu/undergraduate/research/reu/proceedings-archive).
Reference: A.-S. Hirst, R. Linder, and D. Malmuth, *Self-Similarity in Level Set Trees of
Geometric Random Walks*, Oregon State University REU report, August 12, 2016, 1–11.
-/

noncomputable section

namespace Hirst2016Self

open MeasureTheory ProbabilityTheory
open scoped Topology
open Finset

/-- The integer increment law of Definition 3.1, as a probability measure. Shifting by one before
the sign keeps magnitudes positive even at `r = 1`, and outside the target's hypotheses (positive
sum, nonzero `r₁`, `r₂`) the law is a junk value. -/
def kernel (p₁ p₂ : ℝ) (r₁ r₂ : unitInterval)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hpSumLe : p₁ + p₂ ≤ 1) :
    ProbabilityMeasure ℤ :=
  { val :=
      ENNReal.ofReal p₁ • (geometricMeasure r₁).map (fun n : ℕ ↦ (n : ℤ) + 1) +
        ENNReal.ofReal (1 - p₁ - p₂) • Measure.dirac 0 +
        ENNReal.ofReal p₂ • (geometricMeasure r₂).map (fun n : ℕ ↦ -((n : ℤ) + 1))
    property := by
      refine { measure_univ := ?_ }
      have hzero : 0 ≤ 1 - p₁ - p₂ := by
        rw [sub_sub]
        exact sub_nonneg.mpr hpSumLe
      simp only [Measure.add_apply, Measure.smul_apply,
        measure_univ, smul_eq_mul, mul_one]
      rw [add_assoc, ← ENNReal.ofReal_add hzero hp₂, sub_add_cancel,
        ← ENNReal.ofReal_add hp₁ (le_trans hzero (sub_le_self _ hp₂))]
      simp [sub_eq_add_neg] }

open scoped Classical in
/-- Supports of all attained-height superlevel components of the sampled path. -/
def levelComponents {N : ℕ} (x : Fin N → ℤ) : Finset (Finset (Fin N)) :=
  {A ∈ (Finset.univ : Finset (Fin N)).powerset |
    ∃ h : Fin N, ∃ i : {j : Fin N // x h ≤ x j},
      A = ({j | ∃ hj : x h ≤ x j,
        ((SimpleGraph.pathGraph N).induce {k | x h ≤ x k}).Reachable i ⟨j, hj⟩} :
          Finset (Fin N))}

open scoped Classical in
/-- Horton-Strahler order on the superlevel component hierarchy. -/
def hortonRank {N : ℕ} (x : Fin N → ℤ) : Finset (Fin N) → ℕ :=
  Finset.strongInduction fun A rec ↦
    let C := {B ∈ levelComponents x |
      B ⊂ A ∧ ∀ D ∈ levelComponents x, B ⊂ D → ¬D ⊂ A}
    let order : {B // B ∈ C} → ℕ := fun B ↦
      rec B.1 (Finset.mem_filter.mp B.2).2.1
    let orders := C.attach
    let M := orders.sup order
    if C.Nonempty then
      if 2 ≤ #{B ∈ orders | order B = M} then M + 1 else M
    else 1

/-- Number of maximal connected branches with the specified Horton-Strahler order. -/
def branchCount {N : ℕ} (x : Fin N → ℤ) (k : ℕ) : ℕ :=
  Nat.card
    (((SimpleGraph.hasse {A : Finset (Fin N) // A ∈ levelComponents x}).induce
      {A | hortonRank x A.1 = k}).ConnectedComponent)

/-- **Conjecture 3.11**. The geometric-walk family has ratio-asymptotic Horton exponent four exactly
when its increment mean is zero.

The finite-prefix reading follows the cited 2012 finite-chain construction; both directions,
one-sided weights, laziness and degenerate finite samples are retained. -/
theorem conjecture_3_11 (p₁ p₂ : ℝ) (r₁ r₂ : unitInterval)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp : 0 < p₁ + p₂)
    (hp_le : p₁ + p₂ ≤ 1) (hr₁ : 0 < (r₁ : ℝ)) (hr₂ : 0 < (r₂ : ℝ)) :
    (∃ a : ℕ → ℝ,
      (∀ k ≥ 1, 0 ≤ a k) ∧
      (∀ k ≥ 1,
        MeasureTheory.TendstoInMeasure
          (MeasureTheory.Measure.infinitePi fun _ : ℕ ↦
            (kernel p₁ p₂ r₁ r₂ hp₁ hp₂ hp_le : MeasureTheory.Measure ℤ))
          (fun N : ℕ ↦ fun w : ℕ → ℤ ↦
            (branchCount (fun i : Fin N ↦ ∑ j ∈ Finset.range i.val, w j) k : ℝ) /
              (N : ℝ)) Filter.atTop (fun _ ↦ a k)) ∧
      ((∀ᶠ k : ℕ in Filter.atTop, 0 < a (k + 1)) ∧
        Filter.Tendsto (fun k : ℕ ↦ a k / a (k + 1)) Filter.atTop (𝓝 4))) ↔
      p₁ / (r₁ : ℝ) - p₂ / (r₂ : ℝ) = 0 := by
  sorry

end Hirst2016Self
