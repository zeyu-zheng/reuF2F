import Mathlib

/-!
# Permutations with Kazhdan-Lusztig polynomial P_id,w(q) = 1 + q^h

Authors: Alexander Woo; appendix by Sara Billey and Jonathan Weed.
Origin: [University of Washington REU 2008](https://sites.math.washington.edu/~reu/papers/2008/).
Reference: A. Woo, with an appendix by S. Billey and J. Weed, *Permutations with
Kazhdan-Lusztig polynomial P_id,w(q) = 1 + q^h*, Electron. J. Combin. **16** (2009), no. 2,
Research Paper 10, 32 pp.; doi:10.37236/76.
-/

noncomputable section

namespace Woo2009Permutations

open Finset Polynomial

/-- The rank matrix (Section 2.1). Both indices are shifted from one to zero. -/
def rank {n : ℕ} (w : Equiv.Perm (Fin n)) (p q : Fin n) : ℕ :=
  #{i | i ≤ p ∧ w i ≤ q}

/-- Bruhat order: reverse componentwise comparison of ranks (Section 2.1). -/
def Bruhat {n : ℕ} (u w : Equiv.Perm (Fin n)) : Prop :=
  ∀ p q : Fin n, rank w p q ≤ rank u p q

instance {n : ℕ} (u w : Equiv.Perm (Fin n)) : Decidable (Bruhat u w) :=
  inferInstanceAs (Decidable (∀ p q : Fin n, rank w p q ≤ rank u p q))

/-- Coxeter length, the number of inversions (Section 2.1). -/
def length {n : ℕ} (w : Equiv.Perm (Fin n)) : ℕ :=
  #{ij : Fin n × Fin n | ij.1 < ij.2 ∧ w ij.2 < w ij.1}

/-- The adjacent transposition swapping positions `i` and `i + 1` (Section 2.1). -/
def simple {n : ℕ} (i : Fin (n - 1)) : Equiv.Perm (Fin n) :=
  Equiv.swap ⟨i.val, by have := i.isLt; omega⟩
    ⟨i.val + 1, by have := i.isLt; omega⟩

/-- The type-A Kazhdan-Lusztig polynomial, by right-descent recursion (Billey-Warrington,
arXiv:math/0102168v1, equation (12.1)). The correction coefficient is zero unless the relevant
length difference is odd. -/
def kl {n : ℕ} (u w : Equiv.Perm (Fin n)) : Polynomial ℤ :=
  if u = w then 1
  else if Bruhat u w then
    let descents := ({i | length (w * simple i) < length w} : Finset (Fin (n - 1)))
    if hd : descents.Nonempty then
      let i := descents.min' hd
      let s := simple i
      let v := w * s
      have hv : length v < length w := (mem_filter.mp (descents.min'_mem hd)).2
      let c : ℕ := if length (u * s) < length u then 1 else 0
      X ^ c * kl u v + X ^ (1 - c) * kl (u * s) v -
        ∑ z : Equiv.Perm (Fin n),
          if hz : Bruhat u z ∧ Bruhat z v ∧ length z < length v ∧
              length (z * s) < length z ∧ (length v - length z) % 2 = 1 then
            C ((kl z v).coeff ((length v - length z - 1) / 2)) *
              X ^ ((length w - length z) / 2) * kl u z
          else 0
    else 0
  else 0
termination_by length w
decreasing_by
  all_goals first | exact hv | exact Nat.lt_trans hz.2.2.1 hv

/-- The permutations indexing the irreducible singular components (Appendix A). They are
encoded as the Bruhat-maximal `u ≤ w` with `P_u,w` not identically one. -/
def maxsing {n : ℕ} (w : Equiv.Perm (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  {u | Bruhat u w ∧ kl u w ≠ 1 ∧
    ∀ v : Equiv.Perm (Fin n), Bruhat v w → kl v w ≠ 1 → Bruhat u v → v = u}

/-- **Conjecture A.5(1)**. If `P_id,w(1) ≤ 3`, the maximal singular locus has at most three
elements.

Only type A and this first numbered assertion are formalized. -/
theorem conjecture_a5_one {n : ℕ} (hn : 0 < n) (w : Equiv.Perm (Fin n))
    (h : (kl 1 w).eval 1 ≤ 3) : #(maxsing w) ≤ 3 := by
  sorry

end Woo2009Permutations
