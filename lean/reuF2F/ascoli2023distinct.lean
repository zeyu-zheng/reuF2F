import Mathlib

/-!
# Distinct Angles and Angle Chains in Three Dimensions

Authors: Ruben Ascoli, Livia Betti, Jacob Lehmann Duke, Xuyan Liu, Wyatt Milgrim,
Steven J. Miller, Eyvindur A. Palsson, Francisco Romero Acosta, and Santiago Velazquez Iannuzzelli.
Origin: [Williams College SMALL REU
2022](https://web.williams.edu/Mathematics/sjmiller/public_html/math/talks/DistingAnglesPresentationYMC2022.pdf).
Reference: R. Ascoli, L. Betti, J. Lehmann Duke, X. Liu, W. Milgrim, S. J. Miller, E. A. Palsson,
F. Romero Acosta, and S. Velazquez Iannuzzelli, *Distinct angles and angle chains in three
dimensions*, Discrete Math. Theor. Comput. Sci. **25** (2023), no. 1, article 2;
doi:10.46298/dmtcs.10037.
-/

noncomputable section

namespace Ascoli2023Distinct

open Finset

/-- General position: no three collinear and no four concyclic points (Section 1). In dimension
three, four coplanar points are still allowed. -/
def InGeneralPosition {d : ℕ} (P : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  (∀ Q ∈ P.powersetCard 3,
    ¬Collinear ℝ (Q : Set (EuclideanSpace ℝ (Fin d)))) ∧
  (∀ Q ∈ P.powersetCard 4,
    ¬EuclideanGeometry.Concyclic (Q : Set (EuclideanSpace ℝ (Fin d))))

/-- **Conjecture 2.3**. Every sufficiently large configuration in general position
in dimension two or three has quadratically many distinct angles with any chosen
point pinned as an endpoint. -/
theorem conjecture_2_3 (d : ℕ) (hd : d = 2 ∨ d = 3) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ,
      ∀ P : Finset (EuclideanSpace ℝ (Fin d)),
        N ≤ #P → InGeneralPosition P →
        ∀ A ∈ P,
          let a := (#((P.erase A).offDiag.image fun bc ↦
            EuclideanGeometry.angle A bc.1 bc.2) : ℝ)
          c * (#P : ℝ) ^ 2 ≤ a ∧ a ≤ C * (#P : ℝ) ^ 2 := by
  sorry

end Ascoli2023Distinct
