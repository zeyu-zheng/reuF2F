import Mathlib

/-!
# Short Zero-Sum Sequences Over Abelian p-Groups of Large Exponent

Author: Sammy Luo.
Origin: [University of Minnesota Duluth REU
2016](https://sites.google.com/view/gallian-reu/additional-information/program-bibliography).
Reference: S. Luo, *Short zero-sum sequences over abelian p-groups of large exponent*, J. Number
Theory **177** (2017), 28-36; arXiv:1608.05157v1.
-/

noncomputable section

namespace Luo2017Short

open scoped Classical in
/-- The least positive length forcing a nonempty zero-sum subsequence (Section 1). -/
def davenportConstant (G : Type*) [AddCommGroup G] [Finite G] : ℕ :=
  letI := Fintype.ofFinite G
  Nat.find (show ∃ d > 0,
      ∀ S : Multiset G, d ≤ S.card →
        ∃ T : Multiset G, T ≤ S ∧ 0 < T.card ∧ T.sum = 0 from by
    have hn : 0 < AddMonoid.exponent G :=
      AddMonoid.ExponentExists.of_finite.exponent_pos
    refine ⟨Fintype.card G * AddMonoid.exponent G + 1, Nat.succ_pos _, ?_⟩
    intro S hS
    have hcount : ∃ g : G, AddMonoid.exponent G ≤ S.count g := by
      by_contra h
      have hlt : ∀ g : G, S.count g < AddMonoid.exponent G := by
        intro g
        exact Nat.lt_of_not_ge (fun hg ↦ h ⟨g, hg⟩)
      have hbound : S.card ≤ Fintype.card G * AddMonoid.exponent G := by
        calc
          S.card = ∑ g : G, S.count g := by
            symm
            exact Multiset.sum_count_eq_card (fun _ _ ↦ Finset.mem_univ _)
          _ ≤ ∑ _g : G, AddMonoid.exponent G :=
            Finset.sum_le_sum (fun g _ ↦ Nat.le_of_lt (hlt g))
          _ = Fintype.card G * AddMonoid.exponent G := by simp
      exact (Nat.not_lt_of_ge hbound) (lt_of_lt_of_le (Nat.lt_succ_self _) hS)
    obtain ⟨g, hg⟩ := hcount
    refine ⟨Multiset.replicate (AddMonoid.exponent G) g,
      Multiset.le_count_iff_replicate_le.mp hg, ?_, ?_⟩
    · simpa using hn
    · rw [Multiset.sum_replicate, AddMonoid.exponent_nsmul_eq_zero])

/-- **Conjecture 5.4** (arXiv v1, pp. 7-8). Every sufficiently long sequence has an
exponent-length zero-sum subsequence or a twice-exponent zero-sum block containing a zero-sum
subsequence in the specified inclusive length interval.

The bounds are rearranged to avoid truncated natural subtraction; repetitions, zero entries,
`p = 2` and the trivial-group convention `n = D = 1` are retained. -/
theorem conjecture_5_4 (p : ℕ) (hp : p.Prime)
    (G : Type*) [AddCommGroup G] [Finite G]
    (hG : IsPGroup p (Multiplicative G)) :
    let n := AddMonoid.exponent G
    let D := davenportConstant G
    ∀ (hD : D + 1 ≤ 2 * n),
      ∀ ell ≥ 1, ∀ (hell_upper : ell + n ≤ D + 1)
        (S : Multiset G) (hS : D + n + ell ≤ S.card + 2),
      (∃ B : Multiset G, B ≤ S ∧ B.card = n ∧ B.sum = 0) ∨
      (∃ B : Multiset G, B ≤ S ∧ B.card = 2 * n ∧ B.sum = 0 ∧
        ∃ C : Multiset G, C ≤ B ∧ C.sum = 0 ∧
          2 * n + ell ≤ C.card + D + 1 ∧ C.card + 1 ≤ n) := by
  sorry

end Luo2017Short
