import Mathlib

/-!
# Cyclic Group Invariants and The Minimal Free Resolution of S over S^{C_n}

Authors: Swapnil Garg, Frank Lu, Kevin Ren, and Brian Sun.
Origin: [University of Minnesota Twin Cities REU
2021](https://www-users.cse.umn.edu/~reiner/REU/REU.html).
Reference: S. Garg, F. Lu, K. Ren, and B. Sun, *Cyclic Group Invariants and The Minimal Free
Resolution of S over S^{C_n}*, REU report, August 2021, 40 pp.
-/

noncomputable section

namespace Garg2021Cyclic

open CategoryTheory
open Finset

/-- The invariant subalgebra for the diagonal cyclic action. Since `y_r` has character `r`,
invariant monomials are those of cyclic weight zero. -/
def invariantRing (n : ℕ) : Subalgebra ℂ (MvPolynomial (Fin n) ℂ) where
  carrier := {p | MvPolynomial.IsWeightedHomogeneous
    (fun r : Fin n ↦ (r.val : ZMod n)) p 0}
  zero_mem' := MvPolynomial.isWeightedHomogeneous_zero _ _ _
  one_mem' := MvPolynomial.isWeightedHomogeneous_one _ _
  add_mem' hp hq := hp.add hq
  mul_mem' hp hq := by simpa using hp.mul hq
  algebraMap_mem' c := MvPolynomial.isWeightedHomogeneous_C _ c

/-- The character-`k` eigenspace, as a module over the invariant ring. -/
def characterModule (n : ℕ) (k : ZMod n) :
    Submodule (invariantRing n) (MvPolynomial (Fin n) ℂ) where
  carrier := {p | MvPolynomial.IsWeightedHomogeneous
    (fun r : Fin n ↦ (r.val : ZMod n)) p k}
  zero_mem' := MvPolynomial.isWeightedHomogeneous_zero _ _ _
  add_mem' hp hq := hp.add hq
  smul_mem' r p hp := by
    change MvPolynomial.IsWeightedHomogeneous _
      ((r : MvPolynomial (Fin n) ℂ) * p) k
    simpa using r.property.mul hp

/-- The module structure of `characterModule n k` over the invariant ring. -/
instance (n : ℕ) (k : ZMod n) : Module (invariantRing n) (characterModule n k) :=
  Submodule.module _

/-- **Conjecture 5.5** (p. 39). The shifts in every homological degree of the minimal free
resolution of a nontrivial character module lie in the stated total-degree interval.

This is the containment conjectured on p. 39, not the stronger support equality of the
introduction; nontrivial characters include nonunits and `n = 2`. Betti numbers count free
summands over integer multidegrees, and the resolution is exact including its augmentation, with
multidegree-preserving matrices having zero constant coefficient. -/
theorem betti_support
    {n : ℕ} (hn : 0 < n) (k : ZMod n) (hk : k ≠ 0)
    (P : ProjectiveResolution
      (ModuleCat.of (invariantRing n) (characterModule n k)))
    (rank : ℕ → ℕ)
    (basis : ∀ i, Module.Basis (Fin (rank i)) (invariantRing n) (P.complex.X i))
    (degree : ∀ i, Fin (rank i) → (Fin n → ℤ))
    (haugmentation : ∀ a : Fin (rank 0),
      MvPolynomial.IsWeightedHomogeneous (fun r : Fin n ↦ Pi.single r (1 : ℤ))
        ((characterModule n k).subtype
          ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
            (ModuleCat.of (invariantRing n) (characterModule n k))).hom.hom
              ((P.π.f 0).hom (basis 0 a)))) (degree 0 a))
    (hmaps : ∀ (i : ℕ) (a : Fin (rank i)) (b : Fin (rank (i + 1))),
      let c : MvPolynomial (Fin n) ℂ :=
        ((basis i).repr ((P.complex.d (i + 1) i).hom (basis (i + 1) b)) a :
          invariantRing n)
      MvPolynomial.constantCoeff c = 0 ∧
        ∀ d ∈ c.support, ∀ r : Fin n,
          (d r : ℤ) + degree i a r = degree (i + 1) b r)
    (i : ℕ) (j : ℤ)
    (hbetti : #{a : Fin (rank i) | ∑ r : Fin n, degree i a r = j} ≠ 0) :
    3 * (i : ℤ) + 1 ≤ j ∧ j ≤ (n : ℤ) * i + n - 1 := by
  sorry

end Garg2021Cyclic
