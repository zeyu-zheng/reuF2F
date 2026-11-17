import Mathlib

/-!
# Harmonic functions and the spectrum of the Laplacian on the Sierpinski carpet

Authors: Matthew Begue, Tristan Kalloniatis, and Robert S. Strichartz.
Origin: [Cornell Mathematics REU](https://arxiv.org/pdf/1201.5136#page=1).
Reference: M. Begue, T. Kalloniatis, and R. S. Strichartz, *Harmonic functions and the spectrum
of the Laplacian on the Sierpinski carpet*, preprint (2012); arXiv:1201.5136v1.
-/

noncomputable section

namespace Begue2012Harmonic

open MeasureTheory Filter
open scoped Topology

/-- The eight retained subsquares in the standard carpet's ternary construction. -/
abbrev CellDigit := {d : Fin 3 × Fin 3 // d ≠ (1, 1)}

instance : Nonempty CellDigit := ⟨⟨(0, 0), by decide⟩⟩

/-- An infinite address in the source's eight-map iterated function system. -/
abbrev Address := ℕ → CellDigit

/-- The geometric point of a carpet address. -/
def addressPoint (a : Address) : ℝ × ℝ :=
  (∑' n : ℕ, (a n).val.1.val * (1 / 3 : ℝ) ^ (n + 1),
   ∑' n : ℕ, (a n).val.2.val * (1 / 3 : ℝ) ^ (n + 1))

/-- The square's eight symmetries, acting on the retained ternary digits. -/
def squareAction (swap flipX flipY : Bool) (d : CellDigit) : CellDigit :=
  let x := if swap then d.val.2 else d.val.1
  let y := if swap then d.val.1 else d.val.2
  ⟨(if flipX then ⟨2 - x.val, by omega⟩ else x,
    if flipY then ⟨2 - y.val, by omega⟩ else y), by
    dsimp [x, y]
    rcases d with ⟨⟨dx, dy⟩, hd⟩
    fin_cases dx <;> fin_cases dy <;> cases swap <;> cases flipX <;>
      cases flipY <;>
      simp_all only [Bool.false_eq_true, Fin.coe_ofNat_eq_mod, Fin.isValue, Fin.mk_one,
        Fin.reduceEq, Fin.reduceFinMk, Fin.zero_eta, Nat.add_one_sub_one, Nat.mod_succ, Nat.one_mod,
        Nat.zero_mod, Prod.mk.injEq, and_false, and_self, and_true, not_false_eq_true,
        not_true_eq_false, tsub_self, tsub_zero, zero_ne_one, ↓reduceIte]
    all_goals exact hd rfl⟩

/-- The address of a point in the level-`m` cell `w`, with tail `a`. -/
def cellAddress {m : ℕ} (w : Fin m → CellDigit) (a : Address) : Address :=
  fun n ↦ if h : n < m then w ⟨n, h⟩ else a (n - m)

/-- Integer lower-left coordinate of a level-`m` cell, in units of `3 ^ (-m)`. -/
def cellCoordinate {m : ℕ} (w : Fin m → CellDigit) : ℕ × ℕ :=
  (∑ i : Fin m, (w i).val.1.val * 3 ^ (m - 1 - i.val),
   ∑ i : Fin m, (w i).val.2.val * 3 ^ (m - 1 - i.val))

/-- BBKT's fold onto `w`, expressed on ternary addresses by reflection parity. -/
def foldAddress {m : ℕ} (w : Fin m → CellDigit) (a : Address) : Address :=
  let sourceCell := cellCoordinate (m := m) (fun i ↦ a i.val)
  let targetCell := cellCoordinate w
  cellAddress w (fun n ↦ squareAction false
    (decide (sourceCell.1 % 2 ≠ targetCell.1 % 2))
    (decide (sourceCell.2 % 2 ≠ targetCell.2 % 2)) (a (n + m)))

/-- The symmetric self-similar probability measure on addresses. -/
def addressMeasure : Measure Address :=
  Measure.infinitePi (fun _ : ℕ ↦ (PMF.uniformOfFintype CellDigit).toMeasure)

instance : IsProbabilityMeasure addressMeasure := by
  unfold addressMeasure
  infer_instance

/-- The canonical carpet energy of Kusuoka--Zhou and BBKT (BBKT, Definition 2.15). Closedness is
with respect to energy plus the `L²` norm, not the uniform norm. -/
structure CarpetEnergy where
  /-- The domain of the energy form, as functions on addresses. -/
  domain : Submodule ℝ (Address → ℝ)
  /-- The symmetric bilinear energy form on its domain. -/
  energy : LinearMap.BilinForm ℝ domain
  continuous_mem : ∀ u : domain, Continuous (u : Address → ℝ)
  factors_mem : ∀ u : domain, Function.FactorsThrough (u : Address → ℝ) addressPoint
  symmetric : energy.IsSymm
  nonnegative : ∀ u : domain, 0 ≤ energy u u
  nonzero : ∃ u : domain, 0 < energy u u
  constant_mem : ∀ c : ℝ, (fun _ : Address ↦ c) ∈ domain
  constant_energy : ∀ c : ℝ,
    energy ⟨(fun _ ↦ c), constant_mem c⟩ ⟨(fun _ ↦ c), constant_mem c⟩ = 0
  markov_mem : ∀ u : domain, (fun a ↦ max 0 (min 1 ((u : Address → ℝ) a))) ∈ domain
  markov_energy : ∀ u : domain,
    energy ⟨(fun a ↦ max 0 (min 1 ((u : Address → ℝ) a))), markov_mem u⟩
      ⟨(fun a ↦ max 0 (min 1 ((u : Address → ℝ) a))), markov_mem u⟩ ≤ energy u u
  closed : ∀ u : ℕ → domain,
    (∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      energy (u m - u n) (u m - u n) +
        ∫ a, (((u m : domain) : Address → ℝ) a - ((u n : domain) : Address → ℝ) a) ^ 2
          ∂addressMeasure < ε) →
    ∃ v : domain, Tendsto (fun n ↦ energy (u n - v) (u n - v) +
      ∫ a, (((u n : domain) : Address → ℝ) a - (v : Address → ℝ) a) ^ 2 ∂addressMeasure)
        atTop (𝓝 0)
  regular : ∀ f : Address → ℝ, Continuous f → Function.FactorsThrough f addressPoint →
    ∀ ε > (0 : ℝ), ∃ u : domain, ∀ a : Address, |(u : Address → ℝ) a - f a| < ε
  strongly_local : ∀ u v : domain,
    (∃ (O : Set (ℝ × ℝ)) (c : ℝ), IsOpen O ∧
      closure (addressPoint '' Function.support (u : Address → ℝ)) ⊆ O ∧
      ∀ a : Address, addressPoint a ∈ O → (v : Address → ℝ) a = c) → energy u v = 0
  fold_mem : ∀ (m : ℕ) (w : Fin m → CellDigit) (u : domain),
    (fun a ↦ (u : Address → ℝ) (foldAddress w a)) ∈ domain
  cell_isometry_mem : ∀ (m : ℕ) (w₁ w₂ : Fin m → CellDigit)
    (swap flipX flipY : Bool) (g : Address → ℝ),
    (fun a ↦ g (fun n ↦ foldAddress w₂ a (n + m))) ∈ domain →
    (fun a ↦ g (fun n ↦ squareAction swap flipX flipY
      (foldAddress w₁ a (n + m)))) ∈ domain
  cell_isometry_energy : ∀ (m : ℕ) (w₁ w₂ : Fin m → CellDigit)
    (swap flipX flipY : Bool) (g : Address → ℝ)
    (hg : (fun a ↦ g (fun n ↦ foldAddress w₂ a (n + m))) ∈ domain),
    energy ⟨(fun a ↦ g (fun n ↦ squareAction swap flipX flipY
        (foldAddress w₁ a (n + m)))),
      cell_isometry_mem m w₁ w₂ swap flipX flipY g hg⟩
      ⟨(fun a ↦ g (fun n ↦ squareAction swap flipX flipY
        (foldAddress w₁ a (n + m)))),
      cell_isometry_mem m w₁ w₂ swap flipX flipY g hg⟩ =
    energy ⟨(fun a ↦ g (fun n ↦ foldAddress w₂ a (n + m))), hg⟩
      ⟨(fun a ↦ g (fun n ↦ foldAddress w₂ a (n + m))), hg⟩
  cell_additivity : ∀ (m : ℕ) (u : domain), energy u u =
    (8 : ℝ) ^ (-(m : ℤ)) * ∑ w : Fin m → CellDigit,
      energy ⟨(fun a ↦ (u : Address → ℝ) (foldAddress w a)), fold_mem m w u⟩
        ⟨(fun a ↦ (u : Address → ℝ) (foldAddress w a)), fold_mem m w u⟩

/-- The three compact boundary-identification fractafolds in Section 4. -/
inductive Fractafold
  | torus | kleinBottle | projectivePlane
  deriving DecidableEq

/-- Generating outer-side identifications, including corner endpoints. The projective case has
two opposite-corner classes, not one four-corner class. -/
def BoundaryMatch (X : Fractafold) (a b : Address) : Prop :=
  let p := addressPoint a
  let q := addressPoint b
  (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = if X = .torus then p.2 else 1 - p.2) ∨
  (p.2 = 0 ∧ q.2 = 1 ∧ q.1 = if X = .projectivePlane then 1 - p.1 else p.1)

/-- The energy domain with matched side traces. Transmission across seams is natural, so it is
not imposed separately. -/
def quotientDomain (E : CarpetEnergy) (X : Fractafold) : Submodule ℝ E.domain where
  carrier := {u | ∀ a b : Address, BoundaryMatch X a b →
    (u : Address → ℝ) a = (u : Address → ℝ) b}
  zero_mem' := by intro a b h; rfl
  add_mem' := by
    intro u v hu hv a b h
    change (u : Address → ℝ) a + (v : Address → ℝ) a =
      (u : Address → ℝ) b + (v : Address → ℝ) b
    rw [hu a b h, hv a b h]
  smul_mem' := by
    intro c u hu a b h
    change c * (u : Address → ℝ) a = c * (u : Address → ℝ) b
    rw [hu a b h]

/-- The real eigenspace of the nonnegative quotient Laplacian. Test functions range over the
whole matched form domain, including seam and corner values. -/
def weakEigenspace (E : CarpetEnergy) (X : Fractafold) (μ : ℝ) :
    Submodule ℝ E.domain where
  carrier := {u | u ∈ quotientDomain E X ∧ ∀ v : E.domain,
    v ∈ quotientDomain E X → E.energy u v =
      μ * ∫ a, (u : Address → ℝ) a * (v : Address → ℝ) a ∂addressMeasure}
  zero_mem' := by
    refine ⟨(quotientDomain E X).zero_mem, ?_⟩
    intro v hv
    simp
  add_mem' := by
    intro u w hu hw
    refine ⟨(quotientDomain E X).add_mem hu.1 hw.1, ?_⟩
    intro v hv
    have hiu : Integrable (fun a ↦ (u : Address → ℝ) a *
        (v : Address → ℝ) a) addressMeasure :=
      ((E.continuous_mem u).mul (E.continuous_mem v)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hiw : Integrable (fun a ↦ (w : Address → ℝ) a *
        (v : Address → ℝ) a) addressMeasure :=
      ((E.continuous_mem w).mul (E.continuous_mem v)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    simp only [map_add, LinearMap.add_apply, hu.2 v hv, hw.2 v hv,
      Submodule.coe_add, Pi.add_apply, add_mul, integral_add hiu hiw, mul_add]
  smul_mem' := by
    intro c u hu
    refine ⟨(quotientDomain E X).smul_mem c hu.1, ?_⟩
    intro v hv
    simp only [map_smul, LinearMap.smul_apply, hu.2 v hv, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
    ring

/-- The inclusive eigenvalue count with multiplicities (4.3). Ranks are finite for this energy,
so the `finrank` junk value `0` does not arise. -/
def eigenvalueCount (E : CarpetEnergy) (X : Fractafold) (t : ℝ) : ℕ :=
  Module.finrank ℝ ((⨆ μ : {r : ℝ // r ≤ t}, weakEigenspace E X μ.val) :
    Submodule ℝ E.domain)

/-- **Unnumbered conjecture** (end of Section 4; restated in Section 8). The counting-function
differences for all three compact carpet fractafolds are uniformly bounded.

The continuum energy model is used, including the projective corner singularities; the energy is
unique up to one common positive scale. -/
theorem counting_difference_bounded (E : CarpetEnergy) :
    ∃ C ≥ (0 : ℝ), ∀ t ≥ (0 : ℝ), ∀ X Y : Fractafold,
      |(eigenvalueCount E X t : ℝ) - (eigenvalueCount E Y t : ℝ)| ≤ C := by
  sorry

end Begue2012Harmonic
