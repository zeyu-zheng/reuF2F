import Mathlib

/-!
# Congruences of Concave Composition Functions

Authors: Keenan Monks and Lynnelle Ye.
Origin: [Emory University REU in Number Theory
2012](https://uva.theopenscholar.com/ken-ono/reus-archive-2012).
Reference: K. Monks and L. Ye, *Congruences of concave composition functions*, INTEGERS **13**
(2013), A61.
-/

namespace Monks2014Congruences

open Finset

/-- Concave compositions of odd length of type 1 of `n`:
`a₁ + ... + aₘ₊₁ + b₁ + ... + bₘ`, with
`a₁ > ... > aₘ₊₁ < bₘ < ... < b₁` and `aₘ₊₁ ≥ 0`. For `m = 0` the right list is empty, so
`([0], [])` contributes the constant term. -/
def concaveOdd1 (n : ℕ) : Set (List ℕ × List ℕ) :=
  {ab |
    ab.1.length = ab.2.length + 1 ∧
    ab.1.IsChain (· > ·) ∧
    ab.2.IsChain (· > ·) ∧
    ((∃ x : ℕ, ab.1.getLast? = some x ∧ ab.2 = []) ∨
      ∃ x y : ℕ, ab.1.getLast? = some x ∧ ab.2.getLast? = some y ∧ x < y) ∧
    ab.1.sum + ab.2.sum = n}

open scoped Classical in
/-- `co₁(n)`, the number of odd type-1 concave compositions of `n`. -/
noncomputable def co1 (n : ℕ) : ℕ :=
  let lists := (Finset.range (n + 1)).powerset.image (fun s ↦ s.sort (· ≥ ·));
  #{ab ∈ lists.product lists | ab ∈ concaveOdd1 n}

/-- The strict-endpoint count `E_f(r,a;X)`. The natural ceiling gives exactly the indices below
the real endpoint, including when `X ≤ 0`. -/
noncomputable def E (f : ℕ → ℕ) (r a : ℕ) (X : ℝ) : ℕ :=
  #{n ∈ Finset.range ⌈X⌉₊ | f n % a = r}

open Filter Asymptotics

/-- **Unnumbered conjecture** (after Theorem 1.2, displayed type-1 statement). The residue counts
of odd type-1 concave compositions have uniform linear asymptotics except for odd residues
modulo an even modulus, which have square-root asymptotics. -/
theorem conjecture (a r : ℕ) (ha : 2 ≤ a) (hr : r < a) :
    (Odd a → (fun X : ℝ ↦ (E co1 r a X : ℝ)) ~[atTop] (fun X : ℝ ↦ X / a)) ∧
    (Even a → Even r → (fun X : ℝ ↦ (E co1 r a X : ℝ)) ~[atTop]
      (fun X : ℝ ↦ 2 * X / a)) ∧
    (Even a → Odd r → (fun X : ℝ ↦ (E co1 r a X : ℝ)) ~[atTop]
      (fun X : ℝ ↦ 2 * √(2 * X) / a)) := by
  sorry

end Monks2014Congruences
