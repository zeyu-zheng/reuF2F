import Mathlib

/-!
# On promotion and quasi-tangled labelings of posets

Author: Eliot Hodges.
Origin: [University of Minnesota Duluth REU 2022](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: E. Hodges, *On promotion and quasi-tangled labelings of posets*, Ann. Comb. **28**
(2024), 529–554; doi:10.1007/s00026-023-00646-2.
-/

namespace Hodges2024Promotion

open Finset

open scoped Classical in
/-- Extended promotion, via the equivalent increasing-order Bender–Knuth toggles of
Defant–Kravitz, Proposition 2.2 (Section 2.1). Labels are zero-based. -/
noncomputable def promotion {P : Type*} [PartialOrder P] {n : ℕ}
    (L : P ≃ Fin n) : P ≃ Fin n :=
  (List.finRange (n - 1)).foldl (fun M i ↦
    let a : Fin n := ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩
    let b : Fin n := ⟨i.val + 1, by omega⟩
    if M.symm a < M.symm b then M else M.trans (Equiv.swap a b)) L

open scoped Classical in
/-- **Conjecture 23** (journal; arXiv v1 Conjecture 7.5, Section 7). At most `3(n - 1)!`
labelings remain unsorted after `n - 3` promotions.

The source assumes `n ≥ 3` from Section 3.1 onward. -/
theorem conjecture_23 {P : Type*} [PartialOrder P] [Fintype P]
    (n : ℕ) (hn : 3 ≤ n) (hcard : Fintype.card P = n) :
    #{L : P ≃ Fin n | ¬StrictMono (⇑((promotion^[n - 3]) L))} ≤
      3 * (n - 1).factorial := by
  sorry

end Hodges2024Promotion
