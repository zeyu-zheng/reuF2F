import Mathlib

/-!
# A Computer Implementation of Whitehead's Algorithm

Author: Michael Lau.
Origin: [Oregon State University REU
1997](https://sites.science.oregonstate.edu/math_reu/reucv.html).
Reference: M. Lau, *A computer implementation of Whitehead's algorithm*, Oregon State University
REU report (1997; current PDF dated 2010).
-/

namespace Lau1997Computer

/-- CP equivalence: a signed-letter permutation preserving inversion, followed by a cyclic
rotation (Definitions 3.1-3.2). -/
def CPEquivalent (u v : List (Fin 3 × Bool)) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3 × Bool),
    (∀ x, σ (x.1, !x.2) = ((σ x).1, !(σ x).2)) ∧
      List.IsRotated (u.map σ) v

/-- Reduced CP form: automorphism-minimal length and lexicographic leastness in the CP class,
with letter order `a < b < c < a⁻¹ < b⁻¹ < c⁻¹` (Definition 3.3). -/
def InReducedCPForm (w : FreeGroup (Fin 3)) : Prop :=
  (∀ φ : FreeGroup (Fin 3) ≃* FreeGroup (Fin 3),
    w.norm ≤ (φ w).norm) ∧
  ∀ v : List (Fin 3 × Bool), CPEquivalent w.toWord v →
    ¬List.Lex (fun x y : Fin 3 × Bool ↦
      x.1.val + (if x.2 then 0 else 3) < y.1.val + (if y.2 then 0 else 3))
      v w.toWord

/-- **Conjecture 5.1** (printed p. 21). Prefixing inequivalent reduced CP words by the positive
generator `a` preserves reduced CP form and inequivalence.

The domain includes the identity and pairs of unequal length; CP leastness is not leastness in
the full automorphism orbit, and no post-prefix normalization is performed. -/
theorem conjecture_5_1 (w v : FreeGroup (Fin 3))
    (hw : InReducedCPForm w) (hv : InReducedCPForm v)
    (hne : ¬∃ φ : FreeGroup (Fin 3) ≃* FreeGroup (Fin 3), φ w = v) :
    InReducedCPForm (FreeGroup.of (0 : Fin 3) * w) ∧
      InReducedCPForm (FreeGroup.of (0 : Fin 3) * v) ∧
      ¬∃ φ : FreeGroup (Fin 3) ≃* FreeGroup (Fin 3),
        φ (FreeGroup.of (0 : Fin 3) * w) = FreeGroup.of (0 : Fin 3) * v := by
  sorry

end Lau1997Computer
