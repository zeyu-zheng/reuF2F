import Mathlib

/-!
# A Conjectural Brouwer Inequality for Higher-Dimensional Laplacian Spectra

Author: Rediet Abebe.
Origin: [University of Minnesota Twin Cities REU
2012](https://www-users.cse.umn.edu/~reiner/REU/REU.html).
Reference: R. Abebe, *A conjectural Brouwer inequality for higher-dimensional Laplacian spectra*,
arXiv:1907.07541.
-/

noncomputable section

namespace Abebe2019Conjectural

open Matrix
open Finset

/-- A finite pure `k`-family on the labelled vertex set `Fin n`, represented by its `k`-element
facets (after Definition 11). Only the facets are stored; the complex is their downward closure. -/
structure KFamily (n k : ℕ) where
  /-- The facets of the `k`-family. -/
  facets : Finset (Finset (Fin n))
  /-- Each facet has cardinality `k`. -/
  facet_card : ∀ F ∈ facets, #F = k

namespace KFamily

variable {n k : ℕ}

/-- The boundary matrix `∂_{k-1}` from facets to codimension-one faces. Rows and columns range
over all `(k - 1)`- and `k`-subsets of `[n]`, with zero columns at nonfacets and the zero matrix
for `k = 1` (no augmented boundary). -/
def boundaryMatrix (S : KFamily n k) :
    Matrix {R : Finset (Fin n) // R ∈ Finset.univ.powersetCard (k - 1)}
      {F : Finset (Fin n) // F ∈ Finset.univ.powersetCard k} ℝ :=
  fun R F ↦
    if h : 1 < k ∧ F.1 ∈ S.facets ∧ R.1 ⊆ F.1 ∧ #F.1 = #R.1 + 1 then
      (-1 : ℝ) ^ (#{v ∈ F.1 | v < (F.1 \ R.1).min' (by
        exact Finset.sdiff_nonempty_of_card_lt_card
          (s := R.1) (t := F.1) (by omega))})
    else 0

/-- The source Laplacian matrix `L(S) = ∂_{k-1} ∂ᵀ_{k-1}`. -/
def laplacianMatrix (S : KFamily n k) :
    Matrix {R : Finset (Fin n) // R ∈ Finset.univ.powersetCard (k - 1)}
      {R : Finset (Fin n) // R ∈ Finset.univ.powersetCard (k - 1)} ℝ :=
  S.boundaryMatrix * S.boundaryMatrixᴴ

/-- The `i`th largest Laplacian eigenvalue of the `k`-family. Lean uses `i = 0` for the source's
`λ₁` and pads out-of-range indices by zero. -/
def laplacianEigenvalue (S : KFamily n k) (i : ℕ) : ℝ :=
  letI : Fintype {R : Finset (Fin n) // R ∈ Finset.univ.powersetCard (k - 1)} :=
    Finset.Subtype.fintype (Finset.univ.powersetCard (k - 1))
  if hi : i < Fintype.card {R : Finset (Fin n) // R ∈ Finset.univ.powersetCard (k - 1)} then
    ((by
      simpa [laplacianMatrix] using
        Matrix.isHermitian_mul_conjTranspose_self S.boundaryMatrix :
          S.laplacianMatrix.IsHermitian).eigenvalues₀ ⟨i, hi⟩)
  else 0

end KFamily

/-- **Conjecture 3**. For every pure labelled `k`-family, every partial sum of the Laplacian
spectrum is bounded by `(k - 1) f_{k-1} + binom(t + k - 1, k)`. -/
theorem conjecture_3_brouwer_inequality_for_k_families
    {n k : ℕ} (S : KFamily n k) (hk : 1 ≤ k) (t : ℕ) (ht : 1 ≤ t) :
    (∑ i ∈ Finset.range t, S.laplacianEigenvalue i) ≤
      ((k - 1 : ℕ) : ℝ) * #S.facets + (Nat.choose (t + k - 1) k : ℝ) := by
  sorry

end Abebe2019Conjectural
