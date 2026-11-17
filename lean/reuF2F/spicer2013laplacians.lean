import Mathlib

/-!
# Laplacians on Julia Sets III: Cubic Julia Sets and Formal Matings

Authors: Calum Spicer, Robert S. Strichartz, and Emad Totari.
Origin: [Cornell Mathematics REU 2011](https://pi.math.cornell.edu/~etota001/).
Reference: C. Spicer, R. S. Strichartz, and E. Totari, *Laplacians on Julia Sets III: Cubic
Julia Sets and Formal Matings*, arXiv:1206.2301v1 (2012), 24 pp.
-/

noncomputable section

namespace Spicer2013Laplacians

open Filter MeasureTheory
open scoped Topology

/-- The itinerary for the left-open, right-closed three-arc partition. -/
def kneading (k : ℕ) (t : AddCircle (1 : ℝ)) (j : ℕ) : Fin 3 :=
  let θ : ℝ := 1 / (3 * ((3 : ℝ) ^ k - 1))
  let x : ℝ := AddCircle.equivIoc (1 : ℝ) θ ((3 ^ j : ℕ) • t)
  if x ≤ θ + 1 / 3 then 0 else if x ≤ θ + 2 / 3 then 1 else 2

/-- The angle vertices of the level-`m` circle graph, before identifications. -/
def vertex {k : ℕ} (m : ℕ) (ell : Fin (3 ^ m)) (a : Fin k) : AddCircle (1 : ℝ) :=
  (((3 : ℝ) ^ a.val + ell.val * ((3 : ℝ) ^ k - 1)) /
    ((3 : ℝ) ^ m * ((3 : ℝ) ^ k - 1)) : ℝ)

/-- The oriented length of a type-`a` interval, including the wraparound edge. -/
def edgeLength {k : ℕ} (m : ℕ) (a : Fin k) : ℝ :=
  2 * (3 : ℝ) ^ a.val / ((3 : ℝ) ^ m * ((3 : ℝ) ^ k - 1))

/-- The renormalized finite bilinear energy over every cyclic edge. Weights are `b_a = r ^ a`,
as forced by (2.5) rather than the printed powers after (2.6), and parallel edges and loops are
kept. -/
def graphEnergy (k m : ℕ) : LinearMap.BilinForm ℝ C(AddCircle (1 : ℝ), ℝ) :=
  let r : ℝ := (3 : ℝ) ^ (((k : ℝ) - 1) / k)
  ∑ ell : Fin (3 ^ m), ∑ a : Fin k,
    let x := vertex m ell a
    let y := x + (edgeLength m a : AddCircle (1 : ℝ))
    let d := (ContinuousMap.evalCLM ℝ (M := ℝ) y).toLinearMap -
      (ContinuousMap.evalCLM ℝ (M := ℝ) x).toLinearMap
    ((r ^ m)⁻¹ * r ^ a.val / edgeLength m a) •
      LinearMap.BilinForm.linMulLin d d

/-- The domain `dom(E)`: continuous pullbacks respecting the primary kneading identification,
with bounded renormalized graph energies at every positive level. -/
def energyDomain (k : ℕ) : Submodule ℝ C(AddCircle (1 : ℝ), ℝ) where
  carrier := {u | (∀ x y, kneading k x = kneading k y → u x = u y) ∧
    ∃ C : ℝ, ∀ m : ℕ, graphEnergy k (m + 1) u u ≤ C}
  zero_mem' := by
    refine ⟨by simp, 0, ?_⟩
    intro m
    simp
  add_mem' := by
    intro u v hu hv
    refine ⟨?_, ?_⟩
    · intro x y h
      change u x + v x = u y + v y
      rw [hu.1 x y h, hv.1 x y h]
    · obtain ⟨Cu, huC⟩ := hu.2
      obtain ⟨Cv, hvC⟩ := hv.2
      refine ⟨2 * (Cu + Cv), fun m ↦ ?_⟩
      have hsum : graphEnergy k (m + 1) (u + v) (u + v) ≤
          2 * (graphEnergy k (m + 1) u u + graphEnergy k (m + 1) v v) := by
        simp only [graphEnergy, LinearMap.sum_apply, LinearMap.smul_apply,
          LinearMap.BilinForm.linMulLin_apply, smul_eq_mul]
        simp only [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro ell _
        apply Finset.sum_le_sum
        intro a _
        have hD : 0 ≤ (3 : ℝ) ^ k - 1 := sub_nonneg.mpr (one_le_pow₀ (by norm_num))
        have hL : 0 ≤ edgeLength (m + 1) a := by
          unfold edgeLength
          positivity
        have hc : 0 ≤ (((3 : ℝ) ^ (((k : ℝ) - 1) / k)) ^ (m + 1))⁻¹ *
            ((3 : ℝ) ^ (((k : ℝ) - 1) / k)) ^ a.val / edgeLength (m + 1) a := by
          positivity
        simp only [map_add]
        nlinarith [mul_nonneg hc (sq_nonneg
          (((ContinuousMap.evalCLM ℝ (M := ℝ)
            (vertex (m + 1) ell a + (edgeLength (m + 1) a : AddCircle (1 : ℝ)))).toLinearMap -
            (ContinuousMap.evalCLM ℝ (M := ℝ) (vertex (m + 1) ell a)).toLinearMap) u -
           ((ContinuousMap.evalCLM ℝ (M := ℝ)
            (vertex (m + 1) ell a + (edgeLength (m + 1) a : AddCircle (1 : ℝ)))).toLinearMap -
            (ContinuousMap.evalCLM ℝ (M := ℝ) (vertex (m + 1) ell a)).toLinearMap) v))]
      exact hsum.trans (by linarith [huC m, hvC m])
  smul_mem' := by
    intro c u hu
    refine ⟨?_, ?_⟩
    · intro x y h
      change c * u x = c * u y
      rw [hu.1 x y h]
    · obtain ⟨C, hC⟩ := hu.2
      refine ⟨c ^ 2 * C, fun m ↦ ?_⟩
      have h := mul_le_mul_of_nonneg_left (hC m) (sq_nonneg c)
      simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, pow_two, mul_assoc] using h

/-- The real weak eigenspace of the nonnegative limiting Laplacian. Members satisfy the energy
limit against every function in `dom(E)`, not just finite graph tests. -/
def weakEigenspace (k : ℕ) (μ : ℝ) : Submodule ℝ C(AddCircle (1 : ℝ), ℝ) where
  carrier := {u | u ∈ energyDomain k ∧ ∀ v ∈ energyDomain k,
    Tendsto (fun m : ℕ ↦ graphEnergy k (m + 1) u v) atTop
      (𝓝 (μ * ∫ t : AddCircle (1 : ℝ), u t * v t))}
  zero_mem' := by
    refine ⟨(energyDomain k).zero_mem, ?_⟩
    intro v hv
    simp
  add_mem' := by
    intro u w hu hw
    refine ⟨(energyDomain k).add_mem hu.1 hw.1, ?_⟩
    intro v hv
    have hiu : Integrable (fun t : AddCircle (1 : ℝ) ↦ u t * v t) :=
      (u.continuous.mul v.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hiw : Integrable (fun t : AddCircle (1 : ℝ) ↦ w t * v t) :=
      (w.continuous.mul v.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    simpa only [map_add, LinearMap.add_apply, ContinuousMap.add_apply, add_mul,
      integral_add hiu hiw, mul_add] using (hu.2 v hv).add (hw.2 v hv)
  smul_mem' := by
    intro c u hu
    refine ⟨(energyDomain k).smul_mem c hu.1, ?_⟩
    intro v hv
    simpa only [map_smul, LinearMap.smul_apply, ContinuousMap.smul_apply, smul_eq_mul,
      mul_assoc, integral_const_mul, mul_left_comm μ c] using (hu.2 v hv).const_mul c

/-- The multiplicity recurrence of Conjecture 5.1: `multiplicity k 0 = 2`, and step `j + 1`
maps `m` to `3 (m - 2) + 2` when `k ∣ j + 1` and to `3 (m - 1) + 1` otherwise. -/
def multiplicity (k : ℕ) : ℕ → ℕ
  | 0 => 2
  | j + 1 =>
    if k ∣ j + 1 then 3 * (multiplicity k j - 2) + 2 else 3 * (multiplicity k j - 1) + 1

/-- **Conjecture 5.1**. For every cubic-family parameter and nonzero eigenvalue, the full
multiplicity is the prescribed recurrence at its primitive order.

Identifications use the primary same-kneading definition on p. 4, not its conflicting grouped
display, and weights follow (2.5), not the displayed powers on pp. 6-7; no no-coincidences
principle is assumed. -/
theorem conjecture_5_1 (k : ℕ) (hk : 2 ≤ k) (μ : ℝ) (hμ : μ ≠ 0)
    (heigen : weakEigenspace k μ ≠ ⊥) :
    ∃ j : ℕ, weakEigenspace k (μ / ((3 : ℝ) ^ (((k : ℝ) + 1) / k)) ^ j) ≠ ⊥ ∧
      weakEigenspace k (μ / ((3 : ℝ) ^ (((k : ℝ) + 1) / k)) ^ (j + 1)) = ⊥ ∧
      Module.rank ℝ (weakEigenspace k μ) = (multiplicity k j : Cardinal) := by
  sorry

end Spicer2013Laplacians
