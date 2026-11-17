import Mathlib

/-!
# On Cohen-Macaulayness of S_n-invariant subspace arrangements

Authors: Aaron Brookner, David Corwin, Pavel Etingof, and Steven V Sam.
Origin: [MIT SPUR](https://arxiv.org/pdf/1410.5096v2).
Reference: A. Brookner, D. Corwin, P. Etingof, and S. V. Sam, *On Cohen-Macaulayness of
S_n-invariant subspace arrangements*, Int. Math. Res. Not. IMRN **2016** (2016), no. 7,
2104-2126; doi:10.1093/imrn/rnv200; arXiv:1410.5096v2.
-/

namespace Brookner2016Cohen

open Finset

/-- The subspace `E_λ`: equal coordinates within each consecutive block of the partition, with
parts in decreasing order (Section 1). -/
def E {n : ℕ} (lam : Nat.Partition n) : Set (Fin n → ℂ) :=
  let c : Composition n :=
    { blocks := lam.parts.sort (· ≥ ·)
      blocks_pos := by
        intro i hi
        exact lam.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hi)
      blocks_sum := by
        change (↑(lam.parts.sort (· ≥ ·)) : Multiset ℕ).sum = n
        rw [Multiset.sort_eq, lam.parts_sum] }
  {x | ∀ i j : Fin n, c.index i = c.index j → x i = x j}

/-- The arrangement `X_λ`: the union of all coordinate permutations of `E_λ` (Section 1).
Different blocks may take equal values. -/
def X {n : ℕ} (lam : Nat.Partition n) : Set (Fin n → ℂ) :=
  {x | ∃ σ : Equiv.Perm (Fin n), (fun i ↦ x (σ i)) ∈ E lam}

/-- A complex algebra is Cohen-Macaulay when it is finite locally free over a polynomial
subalgebra (Section 2). Finite locally free is expressed as finite projective. -/
def IsCohenMacaulay (R : Type*) [CommRing R] [Algebra ℂ R] : Prop :=
  ∃ (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] R),
    Function.Injective f ∧
      letI : Algebra (MvPolynomial (Fin d) ℂ) R := f.toRingHom.toAlgebra
      Module.Finite (MvPolynomial (Fin d) ℂ) R ∧
        Module.Projective (MvPolynomial (Fin d) ℂ) R

/-- **Conjecture 7.3** (p. 14). For every partition with at least three distinct part sizes, the
reduced complex arrangement `X_λ` is not Cohen-Macaulay. -/
theorem conjecture_7_3 {n : ℕ} (lam : Nat.Partition n)
    (h : 3 ≤ #lam.parts.toFinset) :
    ¬IsCohenMacaulay
      (MvPolynomial (Fin n) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ (X lam)) := by
  sorry

end Brookner2016Cohen
