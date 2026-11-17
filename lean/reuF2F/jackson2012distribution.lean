import Mathlib

/-!
# Distribution of Eigenvalues of Highly Palindromic Toeplitz Matrices

Authors: Steven Jackson, Steven J. Miller, and Thuy Pham.
Origin: [Williams College SMALL REU 2009](https://arxiv.org/pdf/1003.2010v2).
Reference: S. Jackson, S. J. Miller, and T. Pham, *Distribution of Eigenvalues of Highly
Palindromic Toeplitz Matrices*, J. Theoret. Probab. **25** (2012), 464–495; arXiv:1003.2010v2.
-/

noncomputable section
namespace Jackson2012Distribution

open scoped Topology

/-- The independent-entry label in a symmetric Toeplitz matrix whose first row repeats an even
palindrome of the given half-length. -/
def palindromicLink (halfLength i j : ℕ) : ℕ :=
  let r := Nat.dist i j % (2 * halfLength)
  min r (2 * halfLength - 1 - r)

/-- **Conjecture 5.9**. Every pairing configuration has the same limiting normalized contribution
to an even spectral moment.

The model uses the repeated even palindrome required by Definition 1.1 and Section 4.1 rather than
the inconsistent printed link formula, and pairing counts stand for expected contributions
(Corollary 2.2, Lemma 3.2); no Gaussian-only input law is imposed. -/
theorem configurations_conjecture (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let next : Fin (2 * m) → Fin (2 * m) := fun k ↦
      ⟨(k.val + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩
    ∃ c : ℝ, ∀ p : Equiv.Perm (Fin (2 * m)),
      Function.Involutive p → (∀ k, p k ≠ k) →
      Filter.Tendsto (fun h : ℕ ↦
        (Nat.card { t : Fin (2 * m) → Fin (2 ^ n * (2 * (h + 1))) //
          ∀ k, palindromicLink (h + 1) (t k).val (t (next k)).val =
            palindromicLink (h + 1) (t (p k)).val (t (next (p k))).val } : ℝ) /
          ((2 ^ n * (2 * (h + 1)) : ℕ) : ℝ) ^ (m + 1)) Filter.atTop (𝓝 c) := by sorry

end Jackson2012Distribution
