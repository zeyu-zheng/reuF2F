import Mathlib

/-!
# Generalizing Rules of Three

Author: Ewin Tang.
Origin: [University of Minnesota Twin Cities REU
2017](https://www-users.cse.umn.edu/~reiner/REU/REU.html).
Reference: E. Tang, *Generalizing Rules of Three*, University of Minnesota REU report, 2017.
-/

noncomputable section

namespace Tang2017Generalizing

/-- The one-row Schur Q-function with hook reading: decreasing elementary factors followed by
increasing complete-homogeneous factors (Section 3.1). -/
def schurQ {R : Type*} [Ring R] {N : ℕ} (x : Fin N → R)
    (S : Finset (Fin N)) (k : ℕ) : R :=
  PowerSeries.coeff k
    (((S.sort (· ≥ ·)).map (fun i ↦
      (1 : PowerSeries R) + PowerSeries.C (x i) * PowerSeries.X)).prod *
     ((S.sort (· ≤ ·)).map (fun i ↦
      PowerSeries.invOfUnit
        ((1 : PowerSeries R) - PowerSeries.C (x i) * PowerSeries.X) 1)).prod)

/-- **Conjecture 3.1**. All hook-reading Q-functions of two alphabets commute on every common
subalphabet exactly when the degree-one commutations hold. -/
theorem conjecture_3_1 {R : Type*} [Ring R] {N : ℕ} (x y : Fin N → R) :
    (∀ (S : Finset (Fin N)) (k l : ℕ), Commute (schurQ x S k) (schurQ y S l)) ↔
      (∀ (S : Finset (Fin N)) (k l : ℕ), k = 1 ∨ l = 1 →
        Commute (schurQ x S k) (schurQ y S l)) := by
  sorry

end Tang2017Generalizing
