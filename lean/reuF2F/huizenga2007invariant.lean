import Mathlib

/-!
# Invariant metrics with nonnegative curvature on SO(4) and other Lie groups

Authors: Jack Huizenga and Kristopher Tapp.
Origin: [Williams College SMALL REU](https://web.williams.edu/Mathematics/published.html).
Reference: J. Huizenga and K. Tapp, *Invariant metrics with nonnegative curvature on SO(4) and
other Lie groups*, Michigan Math. J. **55** (2007), no. 3; doi:10.1307/mmj/1197056459;
arXiv:math/0702241.
-/

noncomputable section
namespace Huizenga2007Invariant

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A simple ideal `so(3)` of the orthogonal Lie algebra. -/
abbrev factor := LieAlgebra.Orthogonal.so (Fin 3) ℝ

/-- The Lie algebra `so(4) ≅ so(3) × so(3)` as a product of two commuting simple ideals. -/
abbrev ProductAlgebra := factor × factor

/-- The equal-factor reference metric, with the quaternion bracket normalization. -/
def referenceMetric : LinearMap.BilinForm ℝ ProductAlgebra :=
  let tr := Matrix.traceLinearMap (Fin 3) ℝ ℝ
  let inc := (LieAlgebra.Orthogonal.so (Fin 3) ℝ).incl.toLinearMap
  let m := ((LinearMap.mul ℝ (Matrix (Fin 3) (Fin 3) ℝ)).compl₁₂ inc inc).compr₂ tr
  let l := LinearMap.fst ℝ factor factor
  let r := LinearMap.snd ℝ factor factor
  (- (1 / 8 : ℝ)) • (m.compl₁₂ l l + m.compl₁₂ r r)

/-- Infinitesimal nonnegativity (Definition 3.2), including the vanishing obstruction of
Proposition 3.1. -/
def InfinitesimallyNonnegative (ψ : ProductAlgebra →ₗ[ℝ] ProductAlgebra) : Prop :=
  ∀ X Y : ProductAlgebra, ⁅X, Y⁆ = 0 →
    let q := referenceMetric (⁅X, ψ Y⁆ + ⁅ψ X, Y⁆) ⁅ψ X, ψ Y⁆ +
      referenceMetric ⁅ψ X, X⁆ (ψ ⁅ψ Y, Y⁆) -
      referenceMetric ⁅X, ψ Y⁆ (ψ ⁅X, ψ Y⁆) -
      referenceMetric ⁅X, ψ Y⁆ (ψ ⁅ψ X, Y⁆) -
      referenceMetric ⁅ψ X, Y⁆ (ψ ⁅ψ X, Y⁆)
    0 ≤ q ∧ (q = 0 → ⁅ψ X, ψ Y⁆ - ψ (⁅ψ X, Y⁆ + ⁅X, ψ Y⁆) = 0)

/-- **Unnumbered conjecture** (Section 8, after Theorem 8.1). Every infinitesimally nonnegative
direction without singular eigenvectors comes from the full `S³`-action family (7.3), with a
nonnegatively curved factor metric. -/
theorem regular_infinitesimal_classification
    (ψ : ProductAlgebra →ₗ[ℝ] ProductAlgebra)
    (hself : referenceMetric.IsSelfAdjoint ψ)
    (hnonneg : InfinitesimallyNonnegative ψ)
    (hregular : ∀ (r : ℝ) (V : ProductAlgebra), V ≠ 0 →
      ψ V = r • V → V.1 ≠ 0 ∧ V.2 ≠ 0) :
    ∃ (A : Module.Basis (Fin 3) ℝ factor) (e : factor ≃ₗ⁅ℝ⁆ factor)
      (α β : ℝ) (μ : Fin 3 → ℝ),
      let h := fun U V : factor ↦ referenceMetric (U, 0) (V, 0)
      let a := fun i : Fin 3 ↦ (A i, (0 : factor))
      let b := fun i : Fin 3 ↦ ((0 : factor), e (A i))
      let P := A.constr ℝ (fun i ↦ μ i • A i)
      let Pinv := A.constr ℝ (fun i ↦ (μ i)⁻¹ • A i)
      (∀ i j : Fin 3, referenceMetric (a i) (a j) = if i = j then 1 else 0) ∧
      (∀ i j : Fin 3, referenceMetric (b i) (b j) = if i = j then 1 else 0) ∧
      (∀ i : Fin 3, 0 < μ i) ∧
      (∀ U V : factor,
        0 ≤ (1 / 2 : ℝ) * h (⁅P U, V⁆ + ⁅U, P V⁆) ⁅U, V⁆ -
          (3 / 4 : ℝ) * h (P ⁅U, V⁆) ⁅U, V⁆ +
          (1 / 4 : ℝ) * h (⁅U, P V⁆ + ⁅V, P U⁆) (Pinv (⁅U, P V⁆ + ⁅V, P U⁆)) -
          h ⁅U, P U⁆ (Pinv ⁅V, P V⁆)) ∧
      (∀ i : Fin 3,
        ψ (a i) = (α - 1 / (2 * μ i)) • a i - (1 / (2 * μ i)) • b i ∧
        ψ (b i) = -(1 / (2 * μ i)) • a i + (β - 1 / (2 * μ i)) • b i) := by
  sorry

end Huizenga2007Invariant
