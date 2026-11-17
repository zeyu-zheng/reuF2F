import Mathlib

/-!
# Spectral Analysis of the Kohn Laplacian on Lens Spaces

Authors: Colin Fan, Elena Kim, Zoe Plzak, Ian Shors, Samuel Sottile,
and Yunus E. Zeytuncu.
Origin: [University of Michigan-Dearborn REU](https://doi.org/10.1007/s12220-022-01164-y).
Reference: C. Fan, E. Kim, Z. Plzak, I. Shors, S. Sottile, and Y. E. Zeytuncu, *Spectral
Analysis of the Kohn Laplacian on Lens Spaces*, J. Geom. Anal. **33** (2023), Article 116.
-/

namespace Fan2023Spectral

open Finset

/-- **Unnumbered conjecture** (Introduction, p. 1). The Kohn spectrum determines the
CR-isometry class of every three-dimensional lens space.

The spectrum is encoded by the multiplicities of all positive eigenvalues `2m` (Theorem 1.4 and
Proposition 1.5), since the zero eigenspace is infinite-dimensional for all these spaces. The
conclusion is the unit-and-permutation classification of CR isometry, not Riemannian isometry. -/
theorem kohn_spectral_rigidity (k k' : ℕ) (weights weights' : Fin 2 → ℤ)
    (hk : 0 < k) (hk' : 0 < k')
    (hweights : ∀ i, Int.gcd (weights i) (k : ℤ) = 1)
    (hweights' : ∀ i, Int.gcd (weights' i) (k' : ℤ) = 1) :
    let multiplicity : ℕ → (Fin 2 → ℤ) → ℕ → ℕ := fun k weights m ↦
      #{exponents : (Fin 2 → Fin (m + 1)) × (Fin 2 → Fin (m + 1)) |
          let a := exponents.1
          let b := exponents.2
          0 < (b 0).val + (b 1).val ∧
          ((b 0).val + (b 1).val) * ((a 0).val + (a 1).val + 1) = m ∧
          ((a 0).val = 0 ∨ (b 0).val = 0) ∧
          (k : ℤ) ∣ weights 0 * ((a 0).val - (b 0).val : ℤ) +
            weights 1 * ((a 1).val - (b 1).val : ℤ)}
    ((∀ m > 0, multiplicity k weights m = multiplicity k' weights' m) ↔
        k = k' ∧ ∃ (a : ℤ) (σ : Equiv.Perm (Fin 2)),
          Int.gcd a (k : ℤ) = 1 ∧
          ∀ i, Int.ModEq (k : ℤ) (weights' i) (a * weights (σ i))) := by
  sorry

end Fan2023Spectral
