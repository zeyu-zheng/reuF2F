import Mathlib

/-!
# Families with no perfect matchings

Author: Mihir Singhal.
Origin: [University of Minnesota Duluth REU 2020](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: M. Singhal, *Families with no perfect matchings*, Combin. Theory **1** (2021);
doi:10.5070/C61055359; arXiv:2008.08792v2 (2020).
-/

namespace Singhal2021Families

open Finset

/-- A matching: a subfamily of pairwise disjoint sets. -/
def IsMatching (F M : Finset (Finset ℕ)) : Prop :=
  M ⊆ F ∧ (M : Set (Finset ℕ)).PairwiseDisjoint id

/-- A blocking set: at most `s` vertices, not coverable by a matching of exactly its own
cardinality. -/
def IsBlocking (n s : ℕ) (F : Finset (Finset ℕ)) (B : Finset ℕ) : Prop :=
  B ⊆ Finset.Icc 1 n ∧ #B ≤ s ∧
    ¬∃ M : Finset (Finset ℕ), IsMatching F M ∧
      #M = #B ∧ B ⊆ M.biUnion id

/-- The disjoint blocks `E_1, …, E_(b-1)` of Example 1.3, chosen as successive intervals
outside `[b]`. The index `i` is zero-based. -/
def block (k b i : ℕ) : Finset ℕ :=
  Finset.Ico (b + 1 + i * (k - 1)) (b + 1 + (i + 1) * (k - 1))

/-- The family `E(k,n,b)` built from the canonical disjoint blocks (Example 1.3). The last
distinguished vertex has no exceptional edge of its own. -/
def extremalFamily (k n b : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc (b + 1) n).powersetCard k ∪
    (Finset.range b).biUnion (fun i ↦
      (if i + 1 < b then {insert (i + 1) (block k b i)} else ∅) ∪
      ({S ∈ (Finset.Icc (b + 1) n).powersetCard (k - 1) |
        ¬Disjoint S ((Finset.range i).biUnion (block k b))}).image
          (insert (i + 1)))

/-- **Conjecture 7.4**. The extremal bound holds for all `k ≥ 4` after a threshold depending
only on `b`.

The threshold is at least `2 * b`, which ensures Example 1.3's domain `n ≥ b * k + b`. -/
theorem conjecture_7_4 :
    ∃ s₀ : ℕ → ℕ, (∀ b, 2 * b ≤ s₀ b) ∧
      ∀ (k b s : ℕ) (hk : 4 ≤ k) (hb : 1 ≤ b) (hs : s₀ b ≤ s)
        (F : Finset (Finset ℕ))
        (hF : ∀ A ∈ F, A ⊆ Finset.Icc 1 (k * s) ∧ #A = k)
        (hperfect : ¬∃ M : Finset (Finset ℕ),
          IsMatching F M ∧ M.biUnion id = Finset.Icc 1 (k * s))
        (hblocking : ∀ B : Finset ℕ, #B < b → ¬IsBlocking (k * s) s F B),
        #F ≤ #(extremalFamily k (k * s) b) := by
  sorry

end Singhal2021Families
