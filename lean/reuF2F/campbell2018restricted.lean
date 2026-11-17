import Mathlib

/-!
# Restricted growth function patterns and statistics

Authors: Lindsey R. Campbell, Samantha Dahlberg, Robert Dorward, Jonathan Gerhard,
Thomas Grubb, Carlin Purcell, and Bruce E. Sagan.
Origin: [Michigan State University SURIEM](https://arxiv.org/pdf/1605.04807v3).
Reference: L. R. Campbell, S. Dahlberg, R. Dorward, J. Gerhard, T. Grubb, C. Purcell, and
B. E. Sagan, *Restricted growth function patterns and statistics*, Adv. in Appl. Math. **100**
(2018), 1-42; arXiv:1605.04807v3.
-/

namespace Campbell2018Restricted

open Finset

/-- A positive restricted growth function. The empty prefix has maximum zero, forcing `w 0 = 1`. -/
def IsRGF {n : ℕ} (w : Fin n → ℕ) : Prop :=
  ∀ i, 1 ≤ w i ∧ w i ≤ 1 + ({j | j < i} : Finset (Fin n)).sup w

instance {n : ℕ} (w : Fin n → ℕ) : Decidable (IsRGF w) :=
  inferInstanceAs (Decidable (∀ i,
    1 ≤ w i ∧ w i ≤ 1 + ({j | j < i} : Finset (Fin n)).sup w))

/-- Pattern avoidance: no subsequence has the pattern's order and equalities. -/
def Avoids {n m : ℕ} (w : Fin n → ℕ) (v : Fin m → ℕ) : Prop :=
  ¬∃ f : Fin m → Fin n, StrictMono f ∧
    ∀ i j, (w (f i) ≤ w (f j) ↔ v i ≤ v j)

instance {n m : ℕ} (w : Fin n → ℕ) (v : Fin m → ℕ) : Decidable (Avoids w v) :=
  inferInstanceAs (Decidable (¬∃ f : Fin m → Fin n, StrictMono f ∧
    ∀ i j, (w (f i) ≤ w (f j) ↔ v i ≤ v j)))

/-- The Wachs-White right-bigger statistic, counting distinct values at each position. -/
def rb {n : ℕ} (w : Fin n → ℕ) : ℕ :=
  ∑ i, #(({j | i < j ∧ w i < w j} : Finset (Fin n)).image w)

/-- The right-bigger generating polynomial of the length-`n` RGFs avoiding `v`. -/
noncomputable def RB {m : ℕ} (n : ℕ) (v : Fin m → ℕ) : Polynomial ℕ :=
  ∑ w : Fin n → Fin (n + 1) with IsRGF (fun i ↦ (w i).val) ∧ Avoids (fun i ↦ (w i).val) v,
    Polynomial.X ^ rb (fun i ↦ (w i).val)

/-- **Conjecture 7.1** (arXiv v3). Each fixed coefficient of `RB_n(1221)` eventually stabilizes. -/
theorem conjecture_7_1 (k : ℕ) :
    ∃ N c : ℕ, ∀ n ≥ N, (RB n ![1, 2, 2, 1]).coeff k = c := by
  sorry

end Campbell2018Restricted
