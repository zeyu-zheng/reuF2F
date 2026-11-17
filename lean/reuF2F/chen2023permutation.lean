import Mathlib

/-!
# Permutation Invariant Parking Assortments

Authors: Douglas M. Chen, Pamela E. Harris, J. Carlos Martinez Mori, Eric J. Pabon-Cancel,
and Gabriel Sargent.
Origin: [Summer@ICERM 2022](https://icerm.brown.edu/summerug/2022/).
Reference: D. M. Chen, P. E. Harris, J. C. Martinez Mori, E. J. Pabon-Cancel, and G. Sargent,
*Permutation invariant parking assortments*, Enumer. Combin. Appl. **4**:1 (2024), Article #S2R4;
doi:10.54550/ECA2024V4S1R4.
-/

noncomputable section

namespace Chen2023Permutation

open scoped Classical in
/-- The result of parking a single arriving car of length `len` with preference `pref`. -/
def parkCar (M len pref : ℕ) (occupied : Finset ℕ) : Option (Finset ℕ) :=
  if h : ∃ start ≥ 1, pref ≤ start ∧ start + len - 1 ≤ M ∧
      ∀ t, t < len → start + t ∉ occupied then
    some (occupied ∪ Finset.Ico (Nat.find h) (Nat.find h + len))
  else
    none

/-- The final occupied set, if the cars park successfully in their given order. -/
def parkingOutcome {n : ℕ} (y x : Fin n → ℕ) : Option (Finset ℕ) :=
  (List.finRange n).foldl
    (fun state i ↦ state.bind fun occupied ↦ parkCar (∑ j, y j) (y i) (x i) occupied)
    (some ∅)

/-- `x ∈ PA_n(y)`: all cars park under the preference list `x` for car lengths `y`. -/
def ParkingAssortment {n : ℕ} (y x : Fin n → ℕ) : Prop :=
  (∀ i, 1 ≤ x i ∧ x i ≤ ∑ j, y j) ∧
    ∃ occupied, parkingOutcome y x = some occupied

/-- `x ∈ PA_n^inv(y)`: every rearrangement of the preference list is a parking
assortment for the same ordered list of car lengths. -/
def InvariantParkingAssortment {n : ℕ} (y x : Fin n → ℕ) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), ParkingAssortment y (x ∘ σ)

/-- Minimal invariance: the all-ones preference list is the only invariant parking assortment
for `y`. -/
def MinimallyInvariant {n : ℕ} (y : Fin n → ℕ) : Prop :=
  ∀ x : Fin n → ℕ, InvariantParkingAssortment y x ↔ x = fun _ ↦ 1

/-- **Conjecture 6.1**. For four cars, minimal invariance is equivalent to the displayed Boolean
formula. -/
theorem conjecture_6_1_four_car_boolean_characterization
    (y : Fin 4 → ℕ) (hy : ∀ i, 0 < y i) :
    MinimallyInvariant y ↔
      (y 0 < y 1) ∧ (y 0 < y 2) ∧ (y 0 < y 3) ∧
      (y 1 ≠ y 0 + y 2) ∧ (y 1 ≠ y 0 + y 2 + y 3) ∧
      ((y 1 < y 0 + y 2) ∨ (y 2 ≠ y 0 + y 3)) ∧
      ((y 0 + y 2 < y 1) ∨
        ((y 1 ≠ y 0 + y 3) ∧ ((y 1 < y 2) ∨ (y 2 ≠ y 0 + y 3)))) := by
  sorry

end Chen2023Permutation
