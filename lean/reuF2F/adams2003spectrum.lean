import Mathlib

/-!
# The Spectrum of the Laplacian on the Pentagasket

Authors: Bryant Adams, S. Alex Smith, Robert S. Strichartz, and Alexander Teplyaev.
Origin: Cornell Mathematics REU.
Reference: B. Adams, S. A. Smith, R. S. Strichartz, and A. Teplyaev, *The spectrum of the
Laplacian on the pentagasket*, in Fractals in Graz 2001, Birkhäuser, 2003, pp. 1-24;
doi:10.1007/978-3-0348-8014-5_1.
-/

noncomputable section

namespace Adams2003Spectrum

open Filter MeasureTheory
open scoped Topology

/-- The affine address map for the incidence-corrected pentagasket. -/
def addressMap : ContinuousMap (ℕ → ZMod 5) ℂ :=
  let ρ : ℝ := (3 - √5) / 2
  { toFun := fun a ↦ ∑' n : ℕ,
      ((ρ ^ n * (1 - ρ) : ℝ) : ℂ) * ZMod.stdAddChar (a n)
    continuous_toFun := by
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
      have hn := Real.sqrt_nonneg (5 : ℝ)
      have hρ₀ : 0 ≤ ρ := by dsimp [ρ]; nlinarith
      have hρ₁ : ρ < 1 := by dsimp [ρ]; nlinarith
      have hsum : Summable (fun n : ℕ ↦ ρ ^ n * (1 - ρ)) :=
        (summable_geometric_of_norm_lt_one (by
          simpa [Real.norm_eq_abs, abs_of_nonneg hρ₀] using hρ₁)).mul_right (1 - ρ)
      apply continuous_tsum (u := fun n : ℕ ↦ ρ ^ n * (1 - ρ))
      · intro n
        exact continuous_const.mul ((continuous_of_discreteTopology :
          Continuous (fun j : ZMod 5 ↦ ZMod.stdAddChar j)).comp (continuous_apply n))
      · exact hsum
      · intro n a
        have hc : 0 ≤ ρ ^ n * (1 - ρ) :=
          mul_nonneg (pow_nonneg hρ₀ n) (by linarith)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
        simp only [ZMod.stdAddChar_apply, Circle.norm_coe, mul_one, le_refl] }

/-- The address of a cell's corner, with the first word letter outermost. -/
def cellCornerAddress {m : ℕ} (w : Fin m → ZMod 5) (i : ZMod 5) :
    ℕ → ZMod 5 :=
  fun n ↦ if h : n < m then w (Fin.mk n h) else i

/-- The source renormalized real bilinear energy, retaining every cell incidence. -/
def graphEnergy (m : ℕ) :
    LinearMap.BilinForm ℝ (ContinuousMap (ℕ → ZMod 5) ℝ) :=
  let p : ℝ := (√161 - 7) / 16
  let q : ℝ := 1 / 2 - p
  let r : ℝ := (√161 - 9) / 8
  ∑ w : Fin m → ZMod 5,
    ∑ i : ZMod 5,
      let d₁ := (ContinuousMap.evalCLM ℝ (M := ℝ)
          (cellCornerAddress w i)).toLinearMap -
        (ContinuousMap.evalCLM ℝ (M := ℝ)
          (cellCornerAddress w (i + 1))).toLinearMap
      let d₂ := (ContinuousMap.evalCLM ℝ (M := ℝ)
          (cellCornerAddress w i)).toLinearMap -
        (ContinuousMap.evalCLM ℝ (M := ℝ)
          (cellCornerAddress w (i + 2))).toLinearMap
      ((r ^ m)⁻¹ * p) • LinearMap.BilinForm.linMulLin d₁ d₁ +
        ((r ^ m)⁻¹ * q) • LinearMap.BilinForm.linMulLin d₂ d₂

/-- Continuous geometric pullbacks with bounded diagonal energy at every level. -/
def energyDomain : Submodule ℝ (ContinuousMap (ℕ → ZMod 5) ℝ) where
  carrier := {u | Function.FactorsThrough u addressMap ∧
    ∃ C : ℝ, ∀ m : ℕ, graphEnergy m u u ≤ C}
  zero_mem' := by
    refine And.intro (by intro a b h; rfl) (Exists.intro 0 ?_)
    intro m
    simp
  add_mem' := by
    intro u v hu hv
    refine And.intro ?_ ?_
    · intro a b h
      change u a + v a = u b + v b
      rw [hu.1 h, hv.1 h]
    · obtain ⟨Cu, huC⟩ := hu.2
      obtain ⟨Cv, hvC⟩ := hv.2
      refine Exists.intro (2 * (Cu + Cv)) (fun m ↦ ?_)
      have hpos : ∀ f, 0 ≤ graphEnergy m f f := by
        intro f
        have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 161 by norm_num)
        have hn := Real.sqrt_nonneg (161 : ℝ)
        have hp : 0 ≤ (√161 - 7) / 16 := by nlinarith
        have hq : 0 ≤ 1 / 2 - (√161 - 7) / 16 := by nlinarith
        have hr : 0 ≤ (√161 - 9) / 8 := by nlinarith
        simp only [graphEnergy, LinearMap.sum_apply, LinearMap.add_apply,
          LinearMap.smul_apply, LinearMap.BilinForm.linMulLin_apply, smul_eq_mul]
        apply Finset.sum_nonneg
        intro w hw
        apply Finset.sum_nonneg
        intro i hi
        apply add_nonneg
        · have h := mul_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg hr m)) hp)
            (sq_nonneg (((ContinuousMap.evalCLM ℝ (M := ℝ)
              (cellCornerAddress w i)).toLinearMap -
              (ContinuousMap.evalCLM ℝ (M := ℝ)
              (cellCornerAddress w (i + 1))).toLinearMap) f))
          simpa only [pow_two, mul_assoc] using h
        · have h := mul_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg hr m)) hq)
            (sq_nonneg (((ContinuousMap.evalCLM ℝ (M := ℝ)
              (cellCornerAddress w i)).toLinearMap -
              (ContinuousMap.evalCLM ℝ (M := ℝ)
              (cellCornerAddress w (i + 2))).toLinearMap) f))
          simpa only [pow_two, mul_assoc] using h
      have hn := hpos (u - v)
      simp only [map_sub, LinearMap.sub_apply] at hn
      have hsum : graphEnergy m (u + v) (u + v) ≤
          2 * (graphEnergy m u u + graphEnergy m v v) := by
        simp only [map_add, LinearMap.add_apply]
        linarith
      exact hsum.trans (by linarith [huC m, hvC m])
  smul_mem' := by
    intro c u hu
    refine And.intro ?_ ?_
    · intro a b h
      change c * u a = c * u b
      rw [hu.1 h]
    · obtain ⟨C, hC⟩ := hu.2
      refine Exists.intro (c ^ 2 * C) (fun m ↦ ?_)
      have h := mul_le_mul_of_nonneg_left (hC m) (sq_nonneg c)
      simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, pow_two, mul_assoc] using h

/-- The complete real weak eigenspace for the eigenvalue `r` (the source's `λ`); `true` selects
Dirichlet and `false` Neumann. -/
def weakEigenspace (dirichlet : Bool) (r : ℝ) :
    Submodule ℝ (ContinuousMap (ℕ → ZMod 5) ℝ) :=
  let μ := Measure.infinitePi
    (fun _ : ℕ ↦ (PMF.uniformOfFintype (ZMod 5)).toMeasure)
  { carrier := {u | u ∈ energyDomain ∧
      (dirichlet = true → ∀ i : ZMod 5, u (fun _ ↦ i) = 0) ∧
      ∀ v ∈ energyDomain,
        (dirichlet = true → ∀ i : ZMod 5, v (fun _ ↦ i) = 0) →
        Tendsto (fun m : ℕ ↦ graphEnergy m u v) atTop
          (𝓝 (r * ∫ a, u a * v a ∂μ))}
    zero_mem' := by
      refine And.intro energyDomain.zero_mem (And.intro (by simp) ?_)
      intro v hv hb
      simp
    add_mem' := by
      intro u w hu hw
      refine And.intro (energyDomain.add_mem hu.1 hw.1) (And.intro ?_ ?_)
      · intro h i
        change u (fun _ ↦ i) + w (fun _ ↦ i) = 0
        rw [hu.2.1 h i, hw.2.1 h i, add_zero]
      · intro v hv hb
        have hiu : Integrable (fun a ↦ u a * v a) μ :=
          (u.continuous.mul v.continuous).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        have hiw : Integrable (fun a ↦ w a * v a) μ :=
          (w.continuous.mul v.continuous).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        simpa only [map_add, LinearMap.add_apply, ContinuousMap.add_apply,
          add_mul, integral_add hiu hiw, mul_add] using
          (hu.2.2 v hv hb).add (hw.2.2 v hv hb)
    smul_mem' := by
      intro c u hu
      refine And.intro (energyDomain.smul_mem c hu.1) (And.intro ?_ ?_)
      · intro h i
        change c * u (fun _ ↦ i) = 0
        rw [hu.2.1 h i, mul_zero]
      · intro v hv hb
        simpa only [map_smul, LinearMap.smul_apply, ContinuousMap.smul_apply,
          smul_eq_mul, mul_assoc, integral_const_mul, mul_left_comm r c] using
          (hu.2.2 v hv hb).const_mul c }

/-- The full complex eigenspace: both real components satisfy the same real weak equation. -/
def complexEigenspace (dirichlet : Bool) (μ : ℝ) :
    Submodule ℂ (ContinuousMap (ℕ → ZMod 5) ℂ) where
  carrier := {u |
    (Complex.reCLM.compLeftContinuous ℝ (ℕ → ZMod 5)) u ∈
      weakEigenspace dirichlet μ ∧
    (Complex.imCLM.compLeftContinuous ℝ (ℕ → ZMod 5)) u ∈
      weakEigenspace dirichlet μ}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    constructor
    · simpa only [map_add] using (weakEigenspace dirichlet μ).add_mem hu.1 hv.1
    · simpa only [map_add] using (weakEigenspace dirichlet μ).add_mem hu.2 hv.2
  smul_mem' := by
    intro c u hu
    constructor
    · have h := (weakEigenspace dirichlet μ).sub_mem
        ((weakEigenspace dirichlet μ).smul_mem c.re hu.1)
        ((weakEigenspace dirichlet μ).smul_mem c.im hu.2)
      convert h using 1
      ext a
      change (c * u a).re = c.re * (u a).re - c.im * (u a).im
      exact Complex.mul_re c (u a)
    · have h := (weakEigenspace dirichlet μ).add_mem
        ((weakEigenspace dirichlet μ).smul_mem c.re hu.2)
        ((weakEigenspace dirichlet μ).smul_mem c.im hu.1)
      convert h using 1
      ext a
      change (c * u a).im = c.re * (u a).im + c.im * (u a).re
      exact Complex.mul_im c (u a)

/-- The same pentagon symmetry acts on every address digit. -/
def addressSymmetry (g : DihedralGroup 5) :
    Homeomorph (ℕ → ZMod 5) (ℕ → ZMod 5) :=
  Homeomorph.piCongrRight fun _ : ℕ ↦
    Equiv.toHomeomorphOfDiscrete {
      toFun := fun j ↦ match g with
        | .r i => j + i
        | .sr i => -j - i
      invFun := fun j ↦ match g with
        | .r i => j - i
        | .sr i => -j - i
      left_inv := by
        cases g <;> intro j <;> dsimp <;> abel
      right_inv := by
        cases g <;> intro j <;> dsimp <;> abel }

/-- The geometric inverse-pullback action, without conjugating function values. -/
noncomputable def functionRepresentation :
    Representation ℂ (DihedralGroup 5) C(ℕ → ZMod 5, ℂ) where
  toFun g :=
    (ContinuousMap.compCLM ℂ ℂ
      { toFun := addressSymmetry g⁻¹,
        continuous_toFun := (addressSymmetry g⁻¹).continuous }).toLinearMap
  map_one' := by
    ext u a
    change u (addressSymmetry ((1 : DihedralGroup 5)⁻¹) a) = u a
    congr 1
    funext n
    change a n + -(0 : ZMod 5) = a n
    simp
  map_mul' g h := by
    ext u a
    change u (addressSymmetry ((g * h)⁻¹) a) =
      u (addressSymmetry h⁻¹ (addressSymmetry g⁻¹ a))
    congr 1
    funext n
    rcases g with i | i <;> rcases h with j | j
    next =>
      change a n + -(i + j) = (a n + -i) + -j
      abel
    next =>
      change -a n - (j - i) = -(a n + -i) - j
      abel
    next =>
      change -a n - (i + j) = (-a n - i) + -j
      abel
    next =>
      change a n + -(j - i) = -(-a n - i) - j
      abel

/-- **Unnumbered conjecture** (Introduction, p. 5). Every primitive eigenspace is irreducible
under the full complex dihedral action.

Dirichlet and Neumann are treated jointly (pp. 6, 8-9); primitive means absent from both
predecessor spectra. The geometry follows the cell incidence, reading the printed `1 / τ` as
`1 / τ ^ 2`, and the weak operator follows (1.3)-(1.7) rather than the factor in (1.12). -/
theorem primitive_eigenspaces_irreducible (dirichlet : Bool) (μ : ℝ)
    (heigen : complexEigenspace dirichlet μ ≠ ⊥)
    (hdirichlet : complexEigenspace true (μ * ((√161 - 9) / 8) / 5) = ⊥)
    (hneumann : complexEigenspace false (μ * ((√161 - 9) / 8) / 5) = ⊥) :
    ∃ W : Subrepresentation functionRepresentation,
      W.toSubmodule = complexEigenspace dirichlet μ ∧
      Representation.IsIrreducible W.toRepresentation := by
  sorry

end Adams2003Spectrum
