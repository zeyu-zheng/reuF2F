import Mathlib

/-!
# Approximate fair loaded dice

Authors: Berlanga, William Gasarch, and Peter Tian.
Origin: [University of Maryland REU-CAAR
2016](https://www.cs.umd.edu/projects/reucaar/highlights-2016.html).
Reference: Berlanga, W. Gasarch, and P. Tian, *Approximate fair loaded dice*, REU-CAAR research
report (2017), 12 pp.
-/

namespace Berlanga2017Approximate

/-- **Conjecture 1.1** (p. 2). The displayed loading attains the global minimum of the sum of
squared total-roll probabilities.

Faces are indexed from zero, shifting every total by the number of dice; one die and two faces
are included, and no uniqueness is asserted. A later theorem settles only the two-dice case. -/
theorem minimum_square_mass (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) :
    let D : ℝ := 2 * (m : ℝ) + ((n : ℝ) - 2) * (2 * (m : ℝ) - 1)
    let pStar : Fin m → Fin n → ℝ := fun i j ↦
      if i.val = 0 then
        if j.val = 0 ∨ j.val + 1 = n then (m : ℝ) / D
        else (2 * (m : ℝ) - 1) / D
      else if j.val = 0 ∨ j.val + 1 = n then 1 / 2 else 0
    let S : (Fin m → Fin n → ℝ) → ℝ := fun p ↦
      ∑ s ∈ Finset.range (m * (n - 1) + 1),
        (∑ a : Fin m → Fin n,
          if (∑ i : Fin m, (a i).val) = s then ∏ i : Fin m, p i (a i)
          else 0) ^ 2
    let C : ℝ := (Nat.factorial (2 * m - 1) : ℝ) /
      ((2 : ℝ) ^ (2 * m - 2) * (Nat.factorial (m - 1) : ℝ) ^ 2 * D)
    (∀ i j, 0 ≤ pStar i j) ∧ (∀ i, ∑ j, pStar i j = 1) ∧
      S pStar = C ∧
      ∀ p : Fin m → Convexity.StdSimplex ℝ (Fin n),
        C ≤ S (fun i j ↦ (p i).weights j) := by
  sorry

end Berlanga2017Approximate
